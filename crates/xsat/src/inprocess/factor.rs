use crate::{
    inprocess::dense::Rewatch,
    options::Opt,
    solver::{idx, not, Solver},
    store::{
        arena::Ref,
        convert::{real, truncate, widen},
        flags::Flag,
        heap::Heap,
        watch::{self, occurrence, Occurrence},
    },
    trace::proof::Proof,
};

const FACTOR: i8 = 1;
const QUOTIENT: i8 = 2;
const NOUNTED: i8 = 4;
const MILLION: f64 = 1e6;
const SMALLEST_CANDIDATE: u32 = 3;

#[derive(Debug)]
struct Quotient {
    factor: u32,
    clauses: Vec<u32>,
    matches: Vec<usize>,
}

#[derive(Debug)]
struct Factoring {
    initial: u32,
    count: Vec<u32>,
    counted: Vec<u32>,
    nounted: Vec<u32>,
    qlauses: Vec<Ref>,
    fresh: Vec<u32>,
    limit: u64,
    quotients: Vec<Quotient>,
    schedule: Heap,
}

fn dense_binaries(watches: &[u32]) -> impl Iterator<Item = u32> + '_ {
    watches.iter().filter_map(|&word| match occurrence(word) {
        Occurrence::Binary(other) => Some(other),
        Occurrence::Large(_) => None,
    })
}

impl Solver {
    fn update_candidate(&self, factoring: &mut Factoring, lit: u32) {
        let size = self.clauses.watches[widen(lit)].len();
        if size > 1 {
            factoring
                .schedule
                .update(lit, real(u64::try_from(size).unwrap_or(u64::MAX)));
            if !factoring.schedule.contains(lit) {
                factoring.schedule.push(lit);
            }
        } else if factoring.schedule.contains(lit) {
            factoring.schedule.pop(lit);
        }
    }

    fn schedule_factorization(&self, factoring: &mut Factoring) {
        for idx in 0..self.vars {
            if !self.active[widen(idx)] {
                continue;
            }
            let lit = 2 * idx;
            if self.flags[widen(idx)].has(Flag::Factor0) {
                self.update_candidate(factoring, lit);
            }
            if self.flags[widen(idx)].has(Flag::Factor1) {
                self.update_candidate(factoring, not(lit));
            }
        }
    }

    fn new_quotient(&mut self, factoring: &mut Factoring, factor: u32) {
        self.marks[widen(factor)] = FACTOR;
        factoring.quotients.push(Quotient {
            factor,
            clauses: Vec::new(),
            matches: Vec::new(),
        });
    }

    fn first_factor(&mut self, factoring: &mut Factoring, factor: u32) -> usize {
        self.new_quotient(factoring, factor);
        let clauses = self.clauses.watches[widen(factor)].clone();
        let size = clauses.len();
        self.statistics.factor_ticks += u64::try_from(size).unwrap_or(u64::MAX);
        if let Some(quotient) = factoring.quotients.last_mut() {
            quotient.clauses = clauses;
        }
        size
    }

    fn single_factor_min_literal(&mut self, c: Ref) -> Option<u32> {
        let mut min_lit = None;
        let mut min_size = 0;
        let mut factors = 0;
        for position in 0..self.clauses.arena.size(c) {
            let other = self.clauses.arena.lit(c, position);
            if self.marks[widen(other)] & FACTOR != 0 {
                factors += 1;
                if factors > 1 {
                    break;
                }
            } else {
                self.marks[widen(other)] |= QUOTIENT;
                let other_size = self.clauses.watches[widen(other)].len();
                if min_lit.is_some() && min_size <= other_size {
                    continue;
                }
                min_lit = Some(other);
                min_size = other_size;
            }
        }
        min_lit.filter(|_| factors == 1)
    }

    fn unmark_quotient_literals(&mut self, c: Ref) {
        for position in 0..self.clauses.arena.size(c) {
            self.marks[widen(self.clauses.arena.lit(c, position))] &= !QUOTIENT;
        }
    }

    fn count_next(factoring: &mut Factoring, next: u32) {
        if factoring.count[widen(next)] == 0 {
            factoring.counted.push(next);
        }
        factoring.count[widen(next)] += 1;
    }

    fn quotient_partner(&self, d: Ref, size: u32) -> Option<u32> {
        if self.clauses.arena.quotient(d) || self.clauses.arena.size(d) != size {
            return None;
        }
        let mut next = None;
        for &other in self.clauses.arena.lits(d) {
            let mark = self.marks[widen(other)];
            if mark & QUOTIENT != 0 {
                continue;
            }
            if mark & (FACTOR | NOUNTED) != 0 || next.is_some() {
                return None;
            }
            next = Some(other);
        }
        next
    }

    fn next_factor(&mut self, factoring: &mut Factoring) -> Option<(u32, u32)> {
        let last = factoring.quotients.len() - 1;
        let clauses = factoring.quotients[last].clauses.clone();
        let initial = factoring.initial;
        let mut ticks = 1 + watch::cache_lines(clauses.len());
        for word in clauses {
            match occurrence(word) {
                Occurrence::Binary(q) => {
                    let q_watches = &self.clauses.watches[widen(q)];
                    ticks += 1 + watch::cache_lines(q_watches.len());
                    for next in dense_binaries(q_watches) {
                        if next > initial
                            || self.marks[widen(next)] & FACTOR != 0
                            || !self.active[widen(idx(next))]
                        {
                            continue;
                        }
                        Solver::count_next(factoring, next);
                    }
                }
                Occurrence::Large(c) => {
                    ticks += 1;
                    if let Some(min_lit) = self.single_factor_min_literal(c) {
                        let size = self.clauses.arena.size(c);
                        let min_watches = self.clauses.watches[widen(min_lit)].clone();
                        ticks += 1 + watch::cache_lines(min_watches.len());
                        for min_word in min_watches {
                            let Occurrence::Large(d) = occurrence(min_word) else {
                                continue;
                            };
                            if c == d {
                                continue;
                            }
                            ticks += 1;
                            let Some(next) = self.quotient_partner(d, size) else {
                                continue;
                            };
                            if next > initial || !self.active[widen(idx(next))] {
                                continue;
                            }
                            self.marks[widen(next)] |= NOUNTED;
                            factoring.nounted.push(next);
                            self.clauses.arena.mark_quotient(d);
                            factoring.qlauses.push(d);
                            Solver::count_next(factoring, next);
                        }
                        for lit in factoring.nounted.drain(..) {
                            self.marks[widen(lit)] &= !NOUNTED;
                        }
                    }
                    self.unmark_quotient_literals(c);
                }
            }
            self.statistics.factor_ticks += ticks;
            ticks = 0;
            if self.statistics.factor_ticks > factoring.limit {
                break;
            }
        }
        for at in factoring.qlauses.drain(..) {
            self.clauses.arena.unmark_quotient(at);
        }
        let mut next = None;
        let mut next_count = 0;
        if self.statistics.factor_ticks <= factoring.limit {
            let mut ties = 0;
            for &lit in &factoring.counted {
                let count = factoring.count[widen(lit)];
                if count < next_count {
                    continue;
                }
                if count == next_count {
                    ties += 1;
                } else {
                    next_count = count;
                    next = Some(lit);
                    ties = 1;
                }
            }
            if next_count < 2 {
                next = None;
            } else if ties > 1 {
                let mut next_score = None;
                for &lit in &factoring.counted {
                    if factoring.count[widen(lit)] != next_count {
                        continue;
                    }
                    let score = self.clauses.watches[widen(lit)].len();
                    if next_score.is_some_and(|best| score <= best) {
                        continue;
                    }
                    next_score = Some(score);
                    next = Some(lit);
                }
            }
        }
        for lit in factoring.counted.drain(..) {
            factoring.count[widen(lit)] = 0;
        }
        next.map(|lit| (lit, next_count))
    }

    fn factorize_next(&mut self, factoring: &mut Factoring, next: u32) {
        let last = factoring.quotients.len() - 1;
        self.new_quotient(factoring, next);
        let clauses = factoring.quotients[last].clauses.clone();
        let mut ticks = 1 + watch::cache_lines(clauses.len());
        let mut next_clauses = Vec::new();
        let mut matches = Vec::new();
        for (i, word) in clauses.into_iter().enumerate() {
            match occurrence(word) {
                Occurrence::Binary(q) => {
                    let q_watches = &self.clauses.watches[widen(q)];
                    ticks += 1 + watch::cache_lines(q_watches.len());
                    if dense_binaries(q_watches).any(|other| other == next) {
                        next_clauses.push(word);
                        matches.push(i);
                    }
                }
                Occurrence::Large(c) => {
                    ticks += 1;
                    if let Some(min_lit) = self.single_factor_min_literal(c) {
                        let size = self.clauses.arena.size(c);
                        let min_watches = self.clauses.watches[widen(min_lit)].clone();
                        ticks += 1 + watch::cache_lines(min_watches.len());
                        for min_word in min_watches {
                            let Occurrence::Large(d) = occurrence(min_word) else {
                                continue;
                            };
                            if c == d {
                                continue;
                            }
                            ticks += 1;
                            if self.clauses.arena.quotient(d) || self.clauses.arena.size(d) != size
                            {
                                continue;
                            }
                            let matching = self.clauses.arena.lits(d).iter().all(|&other| {
                                self.marks[widen(other)] & QUOTIENT != 0 || other == next
                            });
                            if matching {
                                next_clauses.push(min_word);
                                matches.push(i);
                                factoring.qlauses.push(d);
                                self.clauses.arena.mark_quotient(d);
                                break;
                            }
                        }
                    }
                    self.unmark_quotient_literals(c);
                }
            }
        }
        for at in factoring.qlauses.drain(..) {
            self.clauses.arena.unmark_quotient(at);
        }
        self.statistics.factor_ticks += ticks;
        if let Some(quotient) = factoring.quotients.last_mut() {
            quotient.clauses = next_clauses;
            quotient.matches = matches;
        }
    }

    fn best_quotient(factoring: &Factoring) -> Option<(usize, usize)> {
        let mut best = None;
        for (position, quotient) in factoring.quotients.iter().enumerate() {
            let factors = position + 1;
            let quotients = quotient.clauses.len();
            let before = quotients * factors;
            let after = quotients + factors;
            if before > after {
                let delta = before - after;
                if best.is_none_or(|(_, reduction)| reduction < delta) {
                    best = Some((position, delta));
                }
            }
        }
        best
    }

    fn flush_unmatched_clauses(factoring: &mut Factoring, q: usize) {
        let (before, after) = factoring.quotients.split_at_mut(q);
        let prev = &mut before[q - 1];
        let current = &after[0];
        let prev_is_first = q == 1;
        let n = current.clauses.len();
        for (i, &j) in current.matches.iter().enumerate() {
            if !prev_is_first {
                prev.matches[i] = prev.matches[j];
            }
            prev.clauses[i] = prev.clauses[j];
        }
        if !prev_is_first {
            prev.matches.truncate(n);
        }
        prev.clauses.truncate(n);
    }

    fn add_factored_quotient(&mut self, quotient: &Quotient, not_fresh: u32) {
        for &word in &quotient.clauses {
            match occurrence(word) {
                Occurrence::Binary(other) => self.new_binary_clause(not_fresh, other),
                Occurrence::Large(c) => {
                    self.clause.push(not_fresh);
                    for position in 0..self.clauses.arena.size(c) {
                        let other = self.clauses.arena.lit(c, position);
                        if other != quotient.factor {
                            self.clause.push(other);
                        }
                    }
                    let _ = self.new_irredundant_clause();
                    self.clause.clear();
                }
            }
        }
    }

    pub(crate) fn eagerly_remove_watch(&mut self, lit: u32, needle: u32) {
        let watches = &mut self.clauses.watches[widen(lit)];
        if let Some(position) = watches.iter().position(|&word| word == needle) {
            let _ = watches.remove(position);
        }
    }

    fn delete_unfactored(&mut self, quotient: &Quotient) {
        let factor = quotient.factor;
        for &word in &quotient.clauses {
            match occurrence(word) {
                Occurrence::Binary(other) => {
                    self.eagerly_remove_watch(other, watch::binary(factor));
                    self.eagerly_remove_watch(factor, watch::binary(other));
                    self.delete_binary(factor, other);
                }
                Occurrence::Large(c) => {
                    for position in 0..self.clauses.arena.size(c) {
                        self.eagerly_remove_watch(self.clauses.arena.lit(c, position), word);
                    }
                    self.mark_clause_as_garbage(c);
                }
            }
        }
    }

    fn update_factored(&self, factoring: &mut Factoring, quotient: &Quotient) {
        let factor = quotient.factor;
        self.update_candidate(factoring, factor);
        self.update_candidate(factoring, not(factor));
        for &word in &quotient.clauses {
            match occurrence(word) {
                Occurrence::Binary(other) => self.update_candidate(factoring, other),
                Occurrence::Large(c) => {
                    for &lit in self.clauses.arena.lits(c) {
                        if lit != factor {
                            self.update_candidate(factoring, lit);
                        }
                    }
                }
            }
        }
    }

    fn apply_factoring(&mut self, factoring: &mut Factoring, q: usize) -> bool {
        let Some(fresh) = self.fresh_literal() else {
            return false;
        };
        factoring.fresh.push(fresh);
        for p in (1..=q).rev() {
            Solver::flush_unmatched_clauses(factoring, p);
        }
        for p in (0..=q).rev() {
            self.new_binary_clause(fresh, factoring.quotients[p].factor);
        }
        let quotients = std::mem::take(&mut factoring.quotients);
        self.add_factored_quotient(&quotients[q], not(fresh));
        for p in (0..=q).rev() {
            self.delete_unfactored(&quotients[p]);
        }
        for p in (0..=q).rev() {
            self.update_factored(factoring, &quotients[p]);
        }
        factoring.quotients = quotients;
        factoring.count.resize(widen(not(fresh)) + 1, 0);
        true
    }

    fn release_quotients(&mut self, factoring: &mut Factoring) {
        for quotient in factoring.quotients.drain(..) {
            self.marks[widen(quotient.factor)] = 0;
        }
    }

    fn run_factorization(&mut self, limit: u64) -> bool {
        let lits = 2 * self.vars;
        let mut factoring = Factoring {
            initial: lits,
            count: vec![0; widen(lits)],
            counted: Vec::new(),
            nounted: Vec::new(),
            qlauses: Vec::new(),
            fresh: Vec::new(),
            limit,
            quotients: Vec::new(),
            schedule: Heap::default(),
        };
        self.schedule_factorization(&mut factoring);
        let mut done = false;
        while !done && !factoring.schedule.is_empty() {
            let first = factoring.schedule.pop_max();
            if !self.active[widen(idx(first))] {
                continue;
            }
            if self.statistics.factor_ticks > limit || self.terminated() {
                break;
            }
            let flag = Flag::of(first, Flag::Factor0, Flag::Factor1);
            if !self.flags[widen(idx(first))].has(flag) {
                continue;
            }
            self.flags[widen(idx(first))].clear(flag);
            if self.first_factor(&mut factoring, first) > 1 {
                while let Some((next, _)) = self.next_factor(&mut factoring) {
                    self.factorize_next(&mut factoring, next);
                }
                let bound = self.elimination.bound;
                if let Some((q, _)) = Solver::best_quotient(&factoring)
                    .filter(|&(_, reduction)| reduction > widen(bound))
                {
                    done = !self.apply_factoring(&mut factoring, q);
                }
            }
            self.release_quotients(&mut factoring);
        }
        let completed = factoring.schedule.is_empty();
        for &lit in factoring.fresh.iter().rev() {
            self.scores.update(idx(lit), 0.0);
        }
        let fresh: Vec<u32> = factoring.fresh.iter().map(|&lit| idx(lit)).collect();
        self.queue.move_fresh_to_front(&fresh);
        completed
    }

    fn factor_candidates(&self, size_limit: u32) -> Vec<Ref> {
        self.clauses
            .arena
            .refs()
            .take_while(|&at| self.clauses.last_irredundant.is_none_or(|last| at <= last))
            .filter(|&at| {
                !self.clauses.arena.garbage(at)
                    && !self.clauses.arena.redundant(at)
                    && self.clauses.arena.size(at) <= size_limit
            })
            .collect()
    }

    fn connect_clauses_to_factor(&mut self) {
        let size_limit = self.option_u32(Opt::Factorsize);
        if size_limit < SMALLEST_CANDIDATE {
            return;
        }
        let lits = widen(2 * self.vars);
        let mut bincount = vec![0_u32; lits];
        for lit in 0..2 * self.vars {
            if !self.active[widen(idx(lit))] {
                continue;
            }
            for other in watch::binaries(&self.clauses.watches[widen(lit)]) {
                if lit > other {
                    continue;
                }
                bincount[widen(lit)] += 1;
                bincount[widen(other)] += 1;
            }
        }
        let candidates = self.factor_candidates(size_limit);
        let mut largecount = vec![0_u32; lits];
        for &at in &candidates {
            for &lit in self.clauses.arena.lits(at) {
                largecount[widen(lit)] += 1;
            }
        }
        let occurring = |largecount: &[u32], at: Ref| {
            self.clauses
                .arena
                .lits(at)
                .iter()
                .all(|&lit| bincount[widen(lit)] + largecount[widen(lit)] >= 2)
        };
        let mut count = candidates.len();
        for _ in 0..self.option_u32(Opt::Factorcandrounds) {
            let mut new_largecount = vec![0_u32; lits];
            let mut new_count = 0;
            for &at in &candidates {
                if !occurring(&largecount, at) {
                    continue;
                }
                for &lit in self.clauses.arena.lits(at) {
                    new_largecount[widen(lit)] += 1;
                }
                new_count += 1;
            }
            largecount = new_largecount;
            if count == new_count {
                break;
            }
            count = new_count;
        }
        let connected: Vec<Ref> = candidates
            .into_iter()
            .filter(|&at| occurring(&largecount, at))
            .collect();
        for at in connected {
            self.connect_clause(at);
        }
    }

    fn factoring(&self) -> bool {
        if self.option(Opt::Factor) == 0
            || self.active_count == 0
            || self.proof.as_ref().is_some_and(Proof::incremental)
        {
            return false;
        }
        let log_active = truncate(f64::from(self.active_count).log10());
        log_active <= self.statistics.eliminations + u64::from(self.option_u32(Opt::Factordelay))
    }

    pub(crate) fn factor(&mut self) {
        if self.inconsistent
            || !self.factoring()
            || self.factor_marked >= self.statistics.literals_factor
        {
            return;
        }
        self.statistics.factorizations += 1;
        let limit = if self.statistics.factorizations > 1 {
            self.effort_limit(Opt::Factoreffort, self.statistics.factor_ticks)
        } else {
            let initial = u64::from(self.option_u32(Opt::Factoriniticks));
            truncate(real(initial) * MILLION) + self.statistics.factor_ticks
        };
        self.enter_dense_mode(None);
        self.connect_clauses_to_factor();
        let completed = self.run_factorization(limit);
        self.resume_sparse_mode(Rewatch::All, &[]);
        if completed {
            self.factor_marked = self.statistics.literals_factor;
        }
    }
}
