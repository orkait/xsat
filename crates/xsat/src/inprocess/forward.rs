use crate::{
    options::Opt,
    solver::{idx, literal, not, Solver},
    store::{
        arena::{Ref, INITIAL_SEARCHED, INVALID_LIT},
        convert::widen,
        flags::Flag,
        watch::{self, Head, Occurrence},
    },
    trace::proof::Step,
};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Binaries {
    Checked,
    Skipped,
}

impl Solver {
    fn subsume_candidate(&self, lit: u32) -> bool {
        let idx = widen(idx(lit));
        self.active[idx] && self.flags[idx].has(Flag::Subsume)
    }

    fn remove_duplicated_binaries_with_literal(&mut self, lit: u32, delayed: &mut Vec<u32>) {
        let mut watches = std::mem::take(&mut self.clauses.watches[widen(lit)]);
        let mut kept = 0;
        for position in 0..watches.len() {
            let word = watches[position];
            watches[kept] = word;
            kept += 1;
            let Head::Binary(other) = watch::decode(word) else {
                continue;
            };
            if !self.subsume_candidate(other) {
                continue;
            }
            if self.marks[widen(other)] != 0 {
                kept -= 1;
                if lit < other {
                    self.delete_binary(lit, other);
                }
            } else {
                if self.marks[widen(not(other))] != 0 {
                    delayed.push(lit);
                }
                self.marks[widen(other)] = 1;
            }
        }
        watches.truncate(kept);
        for &word in &watches {
            if let Head::Binary(other) = watch::decode(word) {
                self.marks[widen(other)] = 0;
            }
        }
        self.clauses.watches[widen(lit)] = watches;
    }

    fn remove_all_duplicated_binary_clauses(&mut self) {
        let mut delayed = Vec::new();
        for idx in 0..self.vars {
            let lit = literal(idx);
            if self.subsume_candidate(lit) {
                self.remove_duplicated_binaries_with_literal(lit, &mut delayed);
                self.remove_duplicated_binaries_with_literal(not(lit), &mut delayed);
            }
        }
        if delayed.is_empty() {
            return;
        }
        for unit in delayed {
            let value = self.value(unit);
            if value > 0 {
                continue;
            }
            if value < 0 {
                self.proof_lits(Step::Add, &[]);
                self.inconsistent = true;
                break;
            }
            self.learned_unit(unit);
        }
        if !self.inconsistent {
            self.flush_units_while_connected();
        }
    }

    fn find_forward_subsumption_candidates(&mut self) -> Vec<Ref> {
        let clslim = self.option_u32(Opt::Subsumeclslim);
        let end = self.clauses.arena.end();
        let mut candidates = Vec::new();
        let mut at = Ref(0);
        while at < end {
            if self.clauses.last_irredundant.is_some_and(|last| last < at) {
                break;
            }
            let next = self.clauses.arena.next(at);
            if !self.clauses.arena.garbage(at) {
                self.clauses.arena.clear_subsume(at);
                if !self.clauses.arena.redundant(at) && self.clauses.arena.size(at) <= clslim {
                    let mut subsume = 0;
                    for position in 0..self.clauses.arena.size(at) {
                        let lit = self.clauses.arena.lit(at, position);
                        if self.flags[widen(idx(lit))].has(Flag::Subsume) {
                            subsume += 1;
                        }
                        if self.value(lit) > 0 {
                            self.mark_clause_as_garbage(at);
                            break;
                        }
                    }
                    if !self.clauses.arena.garbage(at) && subsume >= 2 {
                        candidates.push(at);
                    }
                }
            }
            at = next;
        }
        candidates
    }

    fn forward_literal(
        &mut self,
        lit: u32,
        binaries: Binaries,
        remove: &mut u32,
        limit: usize,
    ) -> bool {
        let size = self.clauses.watches[widen(lit)].len();
        if size == 0 || size > limit {
            return false;
        }
        let mut watches = std::mem::take(&mut self.clauses.watches[widen(lit)]);
        let mut steps = 1 + watch::cache_lines(size);
        let mut subsume = false;
        let (mut p, mut q) = (0, 0);
        while p < size {
            let word = watches[p];
            watches[q] = word;
            p += 1;
            q += 1;
            match watch::occurrence(word) {
                Occurrence::Binary(other) => {
                    if binaries == Binaries::Skipped {
                        continue;
                    }
                    if self.marks[widen(other)] != 0 {
                        subsume = true;
                        break;
                    }
                    if self.marks[widen(not(other))] != 0 {
                        *remove = not(other);
                        break;
                    }
                }
                Occurrence::Large(at) => {
                    steps += 1;
                    if self.clauses.arena.garbage(at) {
                        q -= 1;
                        continue;
                    }
                    subsume = true;
                    let mut candidate = INVALID_LIT;
                    for position in 0..self.clauses.arena.size(at) {
                        let other = self.clauses.arena.lit(at, position);
                        if self.marks[widen(other)] != 0 {
                            continue;
                        }
                        let value = self.value(other);
                        if value < 0 {
                            continue;
                        }
                        if value > 0 {
                            self.mark_clause_as_garbage(at);
                            candidate = INVALID_LIT;
                            subsume = false;
                            break;
                        }
                        if !subsume {
                            candidate = INVALID_LIT;
                            break;
                        }
                        subsume = false;
                        if self.marks[widen(not(other))] == 0 {
                            break;
                        }
                        candidate = not(other);
                    }
                    if self.clauses.arena.garbage(at) {
                        q -= 1;
                        break;
                    }
                    if subsume {
                        break;
                    }
                    if candidate != INVALID_LIT {
                        *remove = candidate;
                    }
                }
            }
        }
        watches.copy_within(p..size, q);
        watches.truncate(q + size - p);
        self.clauses.watches[widen(lit)] = watches;
        self.statistics.forward_steps += steps;
        subsume
    }

    fn forward_marked_clause(&mut self, at: Ref, remove: &mut u32) -> bool {
        let limit = widen(self.option_u32(Opt::Subsumeocclim));
        self.statistics.forward_steps += 1;
        for position in 0..self.clauses.arena.size(at) {
            let lit = self.clauses.arena.lit(at, position);
            if !self.active[widen(idx(lit))] {
                continue;
            }
            if self.forward_literal(lit, Binaries::Checked, remove, limit)
                || self.forward_literal(not(lit), Binaries::Skipped, remove, limit)
            {
                return true;
            }
        }
        false
    }

    fn unmark_clause(&mut self, at: Ref) {
        for position in 0..self.clauses.arena.size(at) {
            let lit = self.clauses.arena.lit(at, position);
            self.marks[widen(lit)] = 0;
        }
    }

    fn forward_subsumed_clause(&mut self, at: Ref, new_binaries: &mut Vec<u32>) {
        let mut non_false = 0;
        let mut unit = INVALID_LIT;
        for position in 0..self.clauses.arena.size(at) {
            let lit = self.clauses.arena.lit(at, position);
            let value = self.value(lit);
            if value < 0 {
                continue;
            }
            if value > 0 {
                self.mark_clause_as_garbage(at);
                break;
            }
            self.marks[widen(lit)] = 1;
            unit = if non_false == 0 { lit } else { unit ^ lit };
            non_false += 1;
        }
        let garbage = self.clauses.arena.garbage(at);
        if garbage || non_false <= 1 {
            self.unmark_clause(at);
        }
        if garbage {
            return;
        }
        if non_false == 0 {
            self.proof_lits(Step::Add, &[]);
            self.inconsistent = true;
            return;
        }
        let mut remove = INVALID_LIT;
        if non_false > 1 {
            let subsume = self.forward_marked_clause(at, &mut remove);
            self.unmark_clause(at);
            if subsume {
                self.mark_clause_as_garbage(at);
                return;
            }
            if remove == INVALID_LIT {
                return;
            }
        }
        if non_false <= 2 {
            self.learned_unit(if non_false == 1 { unit } else { unit ^ remove });
            self.mark_clause_as_garbage(at);
            self.flush_units_while_connected();
            return;
        }
        self.proof_shrink_clause(at, remove, INVALID_LIT);
        self.mark_removed_literal(remove);
        let mut kept = 0;
        for position in 0..self.clauses.arena.size(at) {
            let lit = self.clauses.arena.lit(at, position);
            if lit == remove || self.value(lit) < 0 {
                continue;
            }
            self.mark_added_literal(lit);
            if non_false > 3 {
                self.clauses.arena.set_lit(at, kept, lit);
            } else {
                new_binaries.push(lit);
            }
            kept += 1;
        }
        if non_false > 3 {
            self.clauses.arena.shrink(at, kept);
            self.clauses.arena.set_searched(at, INITIAL_SEARCHED);
            self.clauses.arena.set_subsume(at);
        } else {
            self.clauses.arena.set_garbage(at);
            let second = new_binaries[new_binaries.len() - 1];
            let first = new_binaries[new_binaries.len() - 2];
            self.watch_binary(first, second);
            self.statistics.clauses_irredundant -= 1;
            self.statistics.clauses_binary += 1;
        }
    }

    fn connect_subsuming(&mut self, occlim: usize, at: Ref) {
        let mut min_lit = None;
        let mut min_occs = usize::MAX;
        for position in 0..self.clauses.arena.size(at) {
            let lit = self.clauses.arena.lit(at, position);
            let idx = widen(idx(lit));
            if !self.active[idx] {
                continue;
            }
            if !self.flags[idx].has(Flag::Subsume) {
                return;
            }
            let occs = self.clauses.watches[widen(lit)].len();
            if min_lit.is_some() && occs > min_occs {
                continue;
            }
            min_lit = Some(lit);
            min_occs = occs;
        }
        if let Some(lit) = min_lit.filter(|_| min_occs <= occlim) {
            self.clauses.watches[widen(lit)].push(watch::large(at));
        }
    }

    fn forward_subsume_all_clauses(&mut self) -> bool {
        let mut candidates = self.find_forward_subsumption_candidates();
        candidates.sort_by_key(|&at| self.clauses.arena.size(at));
        let occlim = widen(self.option_u32(Opt::Subsumeocclim));
        let mut new_binaries = Vec::new();
        let steps_limit = self.effort_limit(Opt::Forwardeffort, self.statistics.forward_steps);
        let mut checked = 0;
        while let Some(&at) = candidates.get(checked) {
            if self.statistics.forward_steps > steps_limit || self.terminated() {
                break;
            }
            checked += 1;
            self.forward_subsumed_clause(at, &mut new_binaries);
            if self.inconsistent {
                break;
            }
            if !self.clauses.arena.garbage(at) {
                self.connect_subsuming(occlim, at);
            }
        }
        for flags in &mut self.flags {
            flags.clear(Flag::Subsume);
        }
        let mut reactivated = 0;
        for (position, &at) in candidates.iter().enumerate() {
            if self.clauses.arena.garbage(at)
                || position < checked && !self.clauses.arena.subsume(at)
            {
                continue;
            }
            for position in 0..self.clauses.arena.size(at) {
                let flags = &mut self.flags[widen(idx(self.clauses.arena.lit(at, position)))];
                if !flags.has(Flag::Subsume) {
                    flags.set(Flag::Subsume);
                    reactivated += 1;
                }
            }
        }
        for pair in new_binaries.rchunks_exact(2) {
            for &lit in pair {
                let flags = &mut self.flags[widen(idx(lit))];
                if !flags.has(Flag::Subsume) {
                    flags.set(Flag::Subsume);
                    reactivated += 1;
                }
            }
        }
        self.inconsistent || reactivated == 0
    }

    pub(crate) fn forward_subsume_during_elimination(&mut self) -> bool {
        self.remove_all_duplicated_binary_clauses();
        self.inconsistent || self.forward_subsume_all_clauses()
    }
}
