use std::cmp::Ordering;

use crate::{
    options::Opt,
    solver::{idx, not, Conflict, Flush, Propagation, Reason, Solver, FALSE, TRUE},
    store::{
        arena::{Kind, Ref, Vivify, INITIAL_SEARCHED, INVALID_LIT},
        convert::{real, truncate, widen},
        watch,
    },
};

const INVALID_TRAIL: u32 = u32::MAX;
const MAX_COUNT: u32 = 0x7fff_ffff;
const UNSORTED_RATIO: u64 = 10;
const SUCCESS_RATE: f64 = 0.01;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Tier {
    Irredundant,
    Tier1,
    Tier2,
    Tier3,
}

#[derive(Clone, Copy, Debug)]
enum Subsuming {
    Binary,
    Large(Ref),
}

#[derive(Clone, Copy, Debug)]
enum Deduced {
    Subsumed(Subsuming),
    Learned(Kind),
}

#[derive(Debug, Default)]
struct Vivifier {
    counts: Vec<u32>,
    schedule: Vec<Ref>,
    sorted: Vec<u32>,
    tried: u64,
    vivified: u64,
}

fn more_occurrences(counts: &[u32], a: u32, b: u32) -> Ordering {
    counts[widen(b)].cmp(&counts[widen(a)]).then(b.cmp(&a))
}

impl Solver {
    fn update_last_irredundant(&mut self, at: Ref) {
        if self.clauses.last_irredundant.is_none_or(|last| last < at) {
            self.clauses.last_irredundant = Some(at);
        }
    }

    fn recompute_and_promote(&mut self, at: Ref) {
        let old_glue = self.clauses.arena.glue(at);
        let new_glue = self.recompute_glue(at, old_glue);
        if new_glue < old_glue {
            self.promote_clause(at, new_glue);
        }
    }

    fn shrink_to_clause(&mut self, at: Ref) {
        let size = self.clause.len();
        self.clauses.arena.lits_mut(at)[..size].copy_from_slice(&self.clause);
        let size = u32::try_from(size).unwrap_or(u32::MAX);
        self.clauses.arena.shrink(at, size);
        self.clauses.arena.set_searched(at, INITIAL_SEARCHED);
        if self.clauses.arena.redundant(at) && self.clauses.arena.glue(at) >= size {
            self.promote_clause(at, size - 1);
        }
    }

    fn simplify_vivification_candidate(&mut self, at: Ref) -> bool {
        self.clause.clear();
        for position in 0..self.clauses.arena.size(at) {
            let lit = self.clauses.arena.lit(at, position);
            let value = self.value(lit);
            if value > 0 {
                self.mark_clause_as_garbage(at);
                return true;
            }
            if value == 0 {
                self.clause.push(lit);
            }
        }
        if self.clause.len() == widen(self.clauses.arena.size(at)) {
            return false;
        }
        if let [first, second] = *self.clause.as_slice() {
            self.new_binary_clause(first, second);
            self.mark_clause_as_garbage(at);
            return true;
        }
        self.proof_replace_clause(at);
        self.shrink_to_clause(at);
        false
    }

    fn tier_glues(&self, tier: Tier) -> (u32, u32) {
        let focused = self.option(Opt::Vivifyfocusedtiers) != 0;
        let tier1 = self.tier1[0];
        let tier2 = tier1.max(if focused {
            self.tier2[0]
        } else {
            self.tier2[1]
        });
        match tier {
            Tier::Irredundant => (0, u32::MAX),
            Tier::Tier1 => (0, tier1),
            Tier::Tier2 => (if tier1 < tier2 { tier1 + 1 } else { 0 }, tier2),
            Tier::Tier3 => (tier2 + 1, u32::MAX),
        }
    }

    fn schedule_vivification_candidates(&mut self, vivifier: &mut Vivifier, tier: Tier) {
        let (lower, upper) = self.tier_glues(tier);
        let mut prioritized = 0;
        for prioritize in [Vivify::Normal, Vivify::Prioritized] {
            let mut next = Ref(0);
            while next < self.clauses.arena.end() {
                let at = next;
                next = self.clauses.arena.next(at);
                if self.clauses.arena.garbage(at) {
                    continue;
                }
                if prioritize == Vivify::Prioritized {
                    for &lit in self.clauses.arena.lits(at) {
                        let count = &mut vivifier.counts[widen(lit)];
                        if *count < MAX_COUNT {
                            *count += 1;
                        }
                    }
                }
                let redundant = self.clauses.arena.redundant(at);
                let glue = self.clauses.arena.glue(at);
                let wanted = match tier {
                    Tier::Irredundant => !redundant,
                    Tier::Tier1 | Tier::Tier2 | Tier::Tier3 => {
                        redundant && lower <= glue && glue <= upper
                    }
                };
                if !wanted || self.clauses.arena.vivify(at) != prioritize {
                    continue;
                }
                if self.simplify_vivification_candidate(at) {
                    continue;
                }
                if prioritize == Vivify::Prioritized {
                    prioritized += 1;
                }
                vivifier.schedule.push(at);
            }
        }
        self.clause.clear();
        if prioritized == 0 {
            for &at in &vivifier.schedule {
                self.clauses.arena.set_vivify(at, Vivify::Prioritized);
            }
        }
        vivifier.tried = 0;
        vivifier.vivified = 0;
    }

    fn worse_candidate(&self, counts: &[u32], r: Ref, s: Ref) -> Ordering {
        let (c, d) = (self.clauses.arena.lits(r), self.clauses.arena.lits(s));
        let priority = |at| self.clauses.arena.vivify(at) == Vivify::Prioritized;
        priority(r)
            .cmp(&priority(s))
            .then_with(|| {
                for (&a, &b) in c.iter().zip(d) {
                    let order = counts[widen(a)].cmp(&counts[widen(b)]);
                    if order != Ordering::Equal {
                        return order;
                    }
                }
                d.len().cmp(&c.len())
            })
            .then_with(|| {
                let last = c.len().min(d.len()) - 1;
                c[last].cmp(&d[last])
            })
            .then(r.cmp(&s))
    }

    fn sort_vivification_candidates(&mut self, vivifier: &mut Vivifier, tier: Tier) {
        let counts = &vivifier.counts;
        if tier == Tier::Irredundant {
            vivifier.schedule.sort_by_key(|&at| {
                let lits = self.clauses.arena.lits(at);
                let mut best = 0;
                for &lit in lits {
                    best = best.max(counts[widen(lit)]);
                }
                let priority = self.clauses.arena.vivify(at) == Vivify::Prioritized;
                (priority, best, !self.clauses.arena.size(at))
            });
            return;
        }
        for &at in &vivifier.schedule {
            self.clauses
                .arena
                .lits_mut(at)
                .sort_by(|&a, &b| more_occurrences(counts, a, b));
        }
        vivifier
            .schedule
            .sort_by(|&r, &s| self.worse_candidate(counts, r, s));
    }

    fn vivify_deduce(
        &mut self,
        candidate: Ref,
        conflict: Option<Conflict>,
        implied: Option<u32>,
        analyzed: &mut Vec<u32>,
    ) -> Deduced {
        let mut redundant = false;
        if let Some(implied) = implied {
            let not_implied = not(implied);
            self.assignment.assigned[widen(idx(not_implied))].analyzed = true;
            analyzed.push(not_implied);
            self.clause.push(implied);
        } else {
            let (lits, reason): (Vec<u32>, Option<Ref>) = match conflict {
                Some(Conflict::Binary(lits)) => (lits.to_vec(), None),
                Some(Conflict::Large(at)) => (self.clauses.arena.lits(at).to_vec(), Some(at)),
                None => (self.clauses.arena.lits(candidate).to_vec(), Some(candidate)),
            };
            if reason.is_some_and(|at| self.clauses.arena.redundant(at)) {
                redundant = true;
            }
            let mut subsumes = reason != Some(candidate);
            for other in lits {
                if self.fixed(other) < 0 {
                    continue;
                }
                self.assignment.assigned[widen(idx(other))].analyzed = true;
                analyzed.push(other);
                if self.marks[widen(other)] <= 0 {
                    subsumes = false;
                }
            }
            if let Some(at) =
                reason.filter(|&at| at != candidate && self.clauses.arena.redundant(at))
            {
                self.recompute_and_promote(at);
            }
            if subsumes {
                return Deduced::Subsumed(reason.map_or(Subsuming::Binary, Subsuming::Large));
            }
        }
        let mut position = 0;
        while position < analyzed.len() {
            let not_lit = analyzed[position];
            let lit = not(not_lit);
            position += 1;
            match self.assignment.assigned[widen(idx(lit))].reason() {
                Reason::Decision | Reason::Unit => self.clause.push(not_lit),
                Reason::Binary(other) => {
                    if self.marks[widen(lit)] > 0 && self.marks[widen(other)] > 0 {
                        return Deduced::Subsumed(Subsuming::Binary);
                    }
                    let assigned = &mut self.assignment.assigned[widen(idx(other))];
                    if !assigned.analyzed {
                        assigned.analyzed = true;
                        analyzed.push(other);
                    }
                }
                Reason::Clause(at) => {
                    if self.clauses.arena.redundant(at) {
                        redundant = true;
                    }
                    let mut subsumes = true;
                    for position in 0..self.clauses.arena.size(at) {
                        let other = self.clauses.arena.lit(at, position);
                        if self.marks[widen(other)] <= 0 {
                            subsumes = false;
                        }
                        if other == lit {
                            continue;
                        }
                        let assigned = &mut self.assignment.assigned[widen(idx(other))];
                        if assigned.level == 0 || assigned.analyzed {
                            continue;
                        }
                        assigned.analyzed = true;
                        analyzed.push(other);
                    }
                    if self.clauses.arena.redundant(at) {
                        self.recompute_and_promote(at);
                    }
                    if subsumes {
                        return Deduced::Subsumed(Subsuming::Large(at));
                    }
                }
            }
        }
        Deduced::Learned(if redundant {
            Kind::Redundant
        } else {
            Kind::Irredundant
        })
    }

    fn vivify_shrinkable(&self, sorted: &[u32], conflict: Option<Conflict>) -> bool {
        if self.clause.len() == sorted.len() {
            return false;
        }
        let mut implied = 0;
        for &lit in sorted {
            let value = self.value(lit);
            if value == 0 {
                return true;
            }
            if value > 0 {
                if conflict.is_some() || implied > 0 {
                    return true;
                }
                implied += 1;
            } else {
                let assigned = self.assignment.assigned[widen(idx(lit))];
                if !assigned.analyzed || assigned.reason() != Reason::Decision {
                    return true;
                }
            }
        }
        false
    }

    fn swap_first_literal_with_best_watch(&mut self, at: Ref, start: usize) {
        let lits = &self.clauses.arena.lits(at)[start..];
        let first = lits[0];
        let mut best_position = 0;
        let mut best_level = self.level_of(first);
        if self.value(first) < 0 {
            for (position, &lit) in lits.iter().enumerate().skip(1) {
                if self.value(lit) < 0 {
                    let level = self.level_of(lit);
                    if level <= best_level {
                        continue;
                    }
                    best_level = level;
                }
                best_position = position;
            }
        }
        if best_position == 0 {
            return;
        }
        let lits = &mut self.clauses.arena.lits_mut(at)[start..];
        lits[0] = lits[best_position];
        lits[best_position] = first;
    }

    fn vivify_unwatch_clause(&mut self, at: Ref) {
        let (first, second) = (self.clauses.arena.lit(at, 0), self.clauses.arena.lit(at, 1));
        watch::remove_blocking(&mut self.clauses.watches[widen(first)], at);
        watch::remove_blocking(&mut self.clauses.watches[widen(second)], at);
    }

    fn vivify_watch_clause(&mut self, at: Ref) {
        self.swap_first_literal_with_best_watch(at, 0);
        self.swap_first_literal_with_best_watch(at, 1);
        let (first, second) = (self.clauses.arena.lit(at, 0), self.clauses.arena.lit(at, 1));
        self.watch_reference(first, second, at);
    }

    fn vivify_learn(&mut self, at: Ref, implied: Option<u32>) {
        match *self.clause.as_slice() {
            [unit] => {
                self.backtrack_without_updating_phases(0);
                self.learned_unit(unit);
                self.assignment.iterating = true;
                self.mark_clause_as_garbage(at);
                let _ = self.propagate_trail(Propagation::Probing, None, Flush::Trail);
            }
            [_, _] => {
                self.backtrack_without_updating_phases(0);
                self.new_learned_binary(at);
            }
            _ => {
                self.proof_replace_clause(at);
                self.vivify_unwatch_clause(at);
                if !self.clauses.arena.redundant(at) {
                    for position in 0..self.clauses.arena.size(at) {
                        self.mark_removed_literal(self.clauses.arena.lit(at, position));
                    }
                    let tail = self.clauses.arena.lits(at)[self.clause.len()..].to_vec();
                    for lit in self.clause.clone().into_iter().chain(tail) {
                        self.mark_added_literal(lit);
                    }
                }
                self.shrink_to_clause(at);
                if implied.is_none() {
                    let size = u32::try_from(self.clause.len()).unwrap_or(u32::MAX);
                    self.backtrack_without_updating_phases(size - 2);
                }
                self.vivify_watch_clause(at);
            }
        }
    }

    fn new_learned_binary(&mut self, at: Ref) {
        if self.clauses.arena.redundant(at) {
            let _ = self.new_redundant_clause(1);
        } else {
            let _ = self.new_irredundant_clause();
        }
        self.mark_clause_as_garbage(at);
    }

    fn vivify_strengthen_after_instantiation(&mut self, at: Ref, remove: u32) {
        self.clause.clear();
        if self.assignment.level == 3 {
            for position in 0..self.clauses.arena.size(at) {
                let lit = self.clauses.arena.lit(at, position);
                if lit != remove && self.level_of(lit) != 0 {
                    self.clause.push(lit);
                }
            }
            self.new_learned_binary(at);
            self.backtrack_without_updating_phases(0);
            return;
        }
        self.proof_shrink_clause(at, remove, INVALID_LIT);
        self.vivify_unwatch_clause(at);
        for position in 0..self.clauses.arena.size(at) {
            let lit = self.clauses.arena.lit(at, position);
            if lit == remove {
                if !self.clauses.arena.redundant(at) {
                    self.mark_removed_literal(lit);
                }
            } else if self.fixed(lit) >= 0 {
                self.clause.push(lit);
                if !self.clauses.arena.redundant(at) {
                    self.mark_added_literal(lit);
                }
            }
        }
        self.shrink_to_clause(at);
        self.clause.clear();
        self.backtrack_without_updating_phases(self.assignment.level - 2);
        self.vivify_watch_clause(at);
    }

    fn reestablish_watch_invariant_for_candidate(&mut self, at: Ref) {
        if self.assignment.level == 0 || self.clauses.arena.garbage(at) {
            return;
        }
        let (first, second) = (self.clauses.arena.lit(at, 0), self.clauses.arena.lit(at, 1));
        let (first_value, second_value) = (self.value(first), self.value(second));
        let level = |solver: &Solver, lit: u32, value: i8| {
            if value == 0 {
                0
            } else {
                solver.level_of(lit)
            }
        };
        let first_level = level(self, first, first_value);
        let second_level = level(self, second, second_value);
        if first_value >= 0 && second_value >= 0 {
            return;
        }
        let new_level = if first_value < 0 && second_value == 0 {
            first_level
        } else if first_value < 0 && second_value > 0 {
            if first_level >= second_level {
                return;
            }
            first_level
        } else if second_value < 0 && first_value == 0 {
            second_level
        } else if second_value < 0 && first_value > 0 {
            if second_level >= first_level {
                return;
            }
            second_level
        } else {
            first_level.min(second_level)
        };
        self.backtrack_without_updating_phases(new_level - 1);
    }

    fn forced_by(&self, at: Ref) -> Option<u32> {
        let mut unit = None;
        for &lit in self.clauses.arena.lits(at) {
            let value = self.value(lit);
            if value < 0 {
                continue;
            }
            if value == 0 || unit.is_some() {
                return None;
            }
            unit = Some(lit);
        }
        unit.filter(|&lit| self.assignment.assigned[widen(idx(lit))].reason() == Reason::Clause(at))
    }

    fn vivify_assume(&mut self, sorted: &[u32], candidate: Ref) -> (Option<Conflict>, Option<u32>) {
        let mut level = 0;
        for &lit in sorted {
            if level < self.assignment.level {
                level += 1;
                if self.assignment.frames[widen(level)].decision == Some(not(lit)) {
                    continue;
                }
                self.backtrack_without_updating_phases(level - 1);
            } else {
                level += 1;
            }
            let value = self.value(lit);
            if value < 0 {
                continue;
            }
            if value > 0 {
                return (None, Some(lit));
            }
            self.internal_assume(not(lit));
            let start = self.assignment.propagate;
            if let Some(conflict) =
                self.propagate_trail(Propagation::Probing, Some(candidate), Flush::Trail)
            {
                return (Some(conflict), None);
            }
            if let Some(&implied) = self.assignment.trail[start..]
                .iter()
                .find(|&&other| self.marks[widen(other)] > 0)
            {
                return (None, Some(implied));
            }
        }
        (None, None)
    }

    #[expect(
        clippy::too_many_lines,
        reason = "the outcome cascade of vivify_clause, kept in Kissat's order"
    )]
    fn vivify_clause(&mut self, vivifier: &mut Vivifier, candidate: Ref) -> bool {
        let mut sorted = std::mem::take(&mut vivifier.sorted);
        sorted.clear();
        for position in 0..self.clauses.arena.size(candidate) {
            let lit = self.clauses.arena.lit(candidate, position);
            let value = self.fixed(lit);
            if value < 0 {
                continue;
            }
            if value > 0 {
                self.mark_clause_as_garbage(candidate);
                vivifier.sorted = sorted;
                return false;
            }
            sorted.push(lit);
        }
        if sorted.len() == 2 {
            vivifier.sorted = sorted;
            return false;
        }
        if let Some(unit) = self.forced_by(candidate) {
            self.backtrack_without_updating_phases(self.level_of(unit) - 1);
        }
        let counts = &vivifier.counts;
        sorted.sort_by(|&a, &b| more_occurrences(counts, a, b));
        for &lit in &sorted {
            self.marks[widen(lit)] = TRUE;
            self.marks[widen(not(lit))] = FALSE;
        }
        let (mut conflict, mut implied) = self.vivify_assume(&sorted, candidate);
        if implied.is_some() {
            let mut better = None;
            let mut better_trail = INVALID_TRAIL;
            for &lit in &sorted {
                if self.value(lit) <= 0 {
                    continue;
                }
                let trail = self.assignment.assigned[widen(idx(lit))].trail;
                if trail > better_trail {
                    continue;
                }
                better_trail = trail;
                better = Some(lit);
            }
            implied = better;
        }
        let level_after_assumptions = self.assignment.level;
        let mut analyzed = Vec::new();
        let deduced = self.vivify_deduce(candidate, conflict, implied, &mut analyzed);
        for &lit in &sorted {
            self.marks[widen(lit)] = 0;
            self.marks[widen(not(lit))] = 0;
        }
        let redundant = self.clauses.arena.redundant(candidate);
        let res = match deduced {
            Deduced::Subsumed(subsuming) => {
                self.mark_clause_as_garbage(candidate);
                if let Subsuming::Large(at) = subsuming {
                    if redundant {
                        if self.clauses.arena.redundant(at)
                            && self.clauses.arena.glue(candidate) < self.clauses.arena.glue(at)
                        {
                            self.promote_clause(at, self.clauses.arena.glue(candidate));
                        }
                    } else if self.clauses.arena.redundant(at) {
                        self.clauses.arena.set_irredundant(at);
                        self.statistics.clauses_redundant -= 1;
                        self.statistics.clauses_irredundant += 1;
                        self.update_last_irredundant(at);
                        for position in 0..self.clauses.arena.size(at) {
                            self.mark_added_literal(self.clauses.arena.lit(at, position));
                        }
                    }
                }
                true
            }
            Deduced::Learned(kind) => {
                if self.vivify_shrinkable(&sorted, conflict) {
                    self.vivify_learn(candidate, implied);
                    true
                } else if implied.is_some() && redundant
                    || (conflict.is_some() || implied.is_some())
                        && !redundant
                        && kind == Kind::Irredundant
                {
                    self.mark_clause_as_garbage(candidate);
                    true
                } else if implied.is_some() {
                    false
                } else {
                    let lit = sorted[sorted.len() - 1];
                    self.backtrack_without_updating_phases(self.assignment.level - 1);
                    self.internal_assume(lit);
                    conflict =
                        self.propagate_trail(Propagation::Probing, Some(candidate), Flush::Trail);
                    if conflict.is_some() {
                        self.vivify_strengthen_after_instantiation(candidate, lit);
                        true
                    } else {
                        self.backtrack_without_updating_phases(self.assignment.level - 2);
                        false
                    }
                }
            }
        };
        for &lit in &analyzed {
            self.assignment.assigned[widen(idx(lit))].analyzed = false;
        }
        self.clause.clear();
        if conflict.is_some() && self.assignment.level == level_after_assumptions {
            self.backtrack_without_updating_phases(self.assignment.level - 1);
        }
        self.reestablish_watch_invariant_for_candidate(candidate);
        vivifier.sorted = sorted;
        res
    }

    fn vivify_round(&mut self, vivifier: &mut Vivifier, tier: Tier, limit: u64) {
        if tier != Tier::Irredundant && self.statistics.clauses_redundant == 0 {
            return;
        }
        self.flush_large_watches();
        self.schedule_vivification_candidates(vivifier, tier);
        if self.option(Opt::Vivifysort) != 0
            && (tier != Tier::Irredundant
                || self.statistics.clauses_irredundant / UNSORTED_RATIO
                    <= self.statistics.clauses_redundant)
        {
            self.sort_vivification_candidates(vivifier, tier);
        }
        self.watch_large_clauses(Ref(0));
        while self.statistics.probing_ticks <= limit && !self.terminated() {
            let Some(candidate) = vivifier.schedule.pop() else {
                break;
            };
            vivifier.tried += 1;
            if self.vivify_clause(vivifier, candidate) {
                vivifier.vivified += 1;
            }
            if self.inconsistent {
                break;
            }
            self.clauses.arena.set_vivify(candidate, Vivify::Normal);
        }
        if self.assignment.level > 0 {
            self.backtrack_without_updating_phases(0);
        }
    }

    pub(crate) fn vivify(&mut self) {
        if self.inconsistent || self.option(Opt::Vivify) == 0 || self.terminated() {
            return;
        }
        let budget = |solver: &Solver, opt| f64::from(solver.option(opt));
        let irredundant = if self.vivify_delay.delaying() {
            0.0
        } else {
            budget(self, Opt::Vivifyirr)
        };
        let (mut tier1, mut tier2, tier3) = if self.statistics.clauses_redundant == 0 {
            (0.0, 0.0, 0.0)
        } else {
            (
                budget(self, Opt::Vivifytier1),
                budget(self, Opt::Vivifytier2),
                budget(self, Opt::Vivifytier3),
            )
        };
        let sum = irredundant + tier1 + tier2 + tier3;
        if sum == 0.0 {
            return;
        }
        let mut limit = self.effort_limit(Opt::Vivifyeffort, self.statistics.probing_ticks);
        let total = real(limit - self.statistics.probing_ticks);
        limit = self.statistics.probing_ticks;
        let focused = self.option(Opt::Vivifyfocusedtiers) != 0;
        let tier2_limit = if focused {
            self.tier2[0]
        } else {
            self.tier2[1]
        };
        if tier1 != 0.0 && tier2 != 0.0 && self.tier1[0] == tier2_limit {
            tier1 += tier2;
            tier2 = 0.0;
        }
        let mut vivifier = Vivifier {
            counts: vec![0; 2 * widen(self.vars)],
            ..Vivifier::default()
        };
        for (tier, share) in [
            (Tier::Tier1, tier1),
            (Tier::Tier2, tier2),
            (Tier::Tier3, tier3),
            (Tier::Irredundant, irredundant),
        ] {
            if share == 0.0 || self.inconsistent || (tier != Tier::Tier1 && self.terminated()) {
                continue;
            }
            limit = truncate(real(limit) + total * share / sum);
            if tier != Tier::Tier1 {
                vivifier.counts.fill(0);
                vivifier.schedule.clear();
            }
            self.vivify_round(&mut vivifier, tier, limit);
            if tier == Tier::Irredundant {
                let tried = real(vivifier.tried);
                let rate = if tried == 0.0 {
                    0.0
                } else {
                    real(vivifier.vivified) / tried
                };
                if rate < SUCCESS_RATE {
                    self.vivify_delay.bump();
                } else {
                    self.vivify_delay.reduce();
                }
            }
        }
    }
}
