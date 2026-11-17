use crate::{
    inprocess::backbone::Watching,
    solver::{idx, not, Reason, Solver, TRUE},
    store::{
        arena::{Ref, INITIAL_SEARCHED},
        convert::widen,
        flags::Flag,
        watch::{self, Head, Occurrence},
    },
    trace::proof::Step,
};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Rewatch {
    FlushEliminated,
    All,
}

impl Solver {
    pub(crate) fn flush_large_watches(&mut self) {
        for lit in 0..2 * self.vars {
            let mut watches = std::mem::take(&mut self.clauses.watches[widen(lit)]);
            let (mut p, mut q) = (0, 0);
            while p < watches.len() {
                let head = watches[p];
                p += 1;
                let Head::Binary(other) = watch::decode(head) else {
                    p += 1;
                    continue;
                };
                if self.marks[widen(other)] != 0 {
                    if lit < other {
                        self.delete_binary(lit, other);
                    }
                } else {
                    self.marks[widen(other)] = TRUE;
                    watches[q] = head;
                    q += 1;
                }
            }
            watches.truncate(q);
            for other in watch::binaries(&watches) {
                self.marks[widen(other)] = 0;
            }
            self.clauses.watches[widen(lit)] = watches;
        }
    }

    pub(crate) fn collect_binaries(&mut self) -> Vec<[u32; 2]> {
        let mut binaries = Vec::new();
        let mut marked = Vec::new();
        for lit in 0..2 * self.vars {
            let watches = std::mem::take(&mut self.clauses.watches[widen(lit)]);
            let lit_value = self.value(lit);
            for other in watch::binaries(&watches) {
                if lit_value == 0 && self.value(other) == 0 {
                    if self.marks[widen(other)] != 0 {
                        if lit < other {
                            self.delete_binary(lit, other);
                        }
                    } else {
                        self.marks[widen(other)] = TRUE;
                        marked.push(other);
                        if lit < other {
                            binaries.push([lit, other]);
                        }
                    }
                } else if lit < other {
                    self.delete_binary(lit, other);
                }
            }
            for other in marked.drain(..) {
                self.marks[widen(other)] = 0;
            }
        }
        binaries
    }

    pub(crate) fn enter_dense_mode(&mut self, binaries: Option<&mut Vec<[u32; 2]>>) {
        match binaries {
            Some(binaries) => *binaries = self.collect_binaries(),
            None => self.flush_large_watches(),
        }
        self.clauses.watching = Watching::Dense;
    }

    pub(crate) fn resume_sparse_mode(&mut self, rewatch: Rewatch, binaries: &[[u32; 2]]) {
        if self.inconsistent {
            return;
        }
        self.flush_large_connected();
        self.clauses.watching = Watching::Sparse;
        for &[first, second] in binaries {
            self.watch_binary(first, second);
        }
        match rewatch {
            Rewatch::FlushEliminated => self.resume_watching_after_elimination(),
            Rewatch::All => self.watch_large_clauses(Ref(0)),
        }
        self.assignment.propagate = 0;
        self.propagate_after_simplifying();
    }

    fn resume_watching_after_elimination(&mut self) {
        let end = self.clauses.arena.end();
        let mut at = Ref(0);
        while at < end {
            let next = self.clauses.arena.next(at);
            if !self.clauses.arena.garbage(at) {
                let collect = self.clauses.arena.lits(at).iter().any(|&lit| {
                    self.value(lit) > 0 || self.flags[widen(idx(lit))].has(Flag::Eliminated)
                });
                if collect {
                    self.mark_clause_as_garbage(at);
                } else {
                    self.sort_literals(at);
                    self.clauses.arena.set_searched(at, INITIAL_SEARCHED);
                    let (first, second) =
                        (self.clauses.arena.lit(at, 0), self.clauses.arena.lit(at, 1));
                    self.watch_reference(first, second, at);
                }
            }
            at = next;
        }
    }

    pub(crate) fn connect_clause(&mut self, at: Ref) {
        for position in 0..self.clauses.arena.size(at) {
            let lit = self.clauses.arena.lit(at, position);
            self.clauses.watches[widen(lit)].push(watch::large(at));
        }
    }

    pub(crate) fn flush_large_connected(&mut self) {
        for watches in &mut self.clauses.watches {
            watches.retain(|&word| matches!(watch::decode(word), Head::Binary(_)));
        }
    }

    pub(crate) fn connect_irredundant_large_clauses(&mut self) {
        let end = self.clauses.arena.end();
        let mut at = Ref(0);
        while at < end {
            if self.clauses.last_irredundant.is_some_and(|last| last < at) {
                break;
            }
            let next = self.clauses.arena.next(at);
            if !self.clauses.arena.redundant(at) && !self.clauses.arena.garbage(at) {
                if self
                    .clauses
                    .arena
                    .lits(at)
                    .iter()
                    .any(|&lit| self.value(lit) > 0)
                {
                    self.mark_clause_as_garbage(at);
                } else {
                    self.connect_clause(at);
                }
            }
            at = next;
        }
    }

    fn dense_propagate_literal(&mut self, lit: u32) -> bool {
        let not_lit = not(lit);
        let mut position = 0;
        while let Some(&word) = self.clauses.watches[widen(not_lit)].get(position) {
            position += 1;
            match watch::occurrence(word) {
                Occurrence::Binary(other) => {
                    let other_value = self.value(other);
                    if other_value > 0 {
                        continue;
                    }
                    if other_value < 0 {
                        return false;
                    }
                    if self.flags[widen(idx(other))].has(Flag::Eliminated) {
                        continue;
                    }
                    self.assign(0, other, Reason::Binary(not_lit));
                }
                Occurrence::Large(at) => {
                    if self.clauses.arena.garbage(at) {
                        continue;
                    }
                    let mut non_false = 0;
                    let mut unit = 0;
                    let mut satisfied = false;
                    for position in 0..self.clauses.arena.size(at) {
                        let other = self.clauses.arena.lit(at, position);
                        if other == not_lit {
                            continue;
                        }
                        let other_value = self.value(other);
                        if other_value < 0 {
                            continue;
                        }
                        if other_value > 0 {
                            satisfied = true;
                            self.mark_clause_as_garbage(at);
                            break;
                        }
                        non_false += 1;
                        if non_false == 1 {
                            unit = other;
                        } else {
                            break;
                        }
                    }
                    if satisfied {
                        continue;
                    }
                    if non_false == 0 {
                        return false;
                    }
                    if non_false == 1 {
                        self.assign(0, unit, Reason::Clause(at));
                    }
                }
            }
        }
        true
    }

    pub(crate) fn dense_propagate(&mut self) -> bool {
        let saved = self.assignment.propagate;
        let mut res = true;
        while res && self.assignment.propagate < self.assignment.trail.len() {
            let lit = self.assignment.trail[self.assignment.propagate];
            self.assignment.propagate += 1;
            res = self.dense_propagate_literal(lit);
        }
        self.statistics.propagations +=
            u64::try_from(self.assignment.propagate - saved).unwrap_or(0);
        if !res {
            self.proof_lits(Step::Add, &[]);
            self.inconsistent = true;
        }
        res
    }

    pub(crate) fn dense_collect(&mut self) {
        let end = self.clauses.arena.end();
        let mut src = Ref(0);
        let mut dst = Ref(0);
        let mut first_reducible = None;
        let mut last_irredundant = None;
        while src != end {
            let next = self.clauses.arena.next(src);
            if !self.clauses.arena.garbage(src) {
                self.clauses.arena.move_clause(src, dst);
                if self.clauses.arena.redundant(dst) {
                    first_reducible.get_or_insert(dst);
                } else {
                    last_irredundant = Some(dst);
                }
                dst = self.clauses.arena.next(dst);
            }
            src = next;
        }
        self.clauses.first_reducible = first_reducible;
        self.clauses.last_irredundant = last_irredundant;
        self.clauses.last_learned = Default::default();
        self.clauses.arena.truncate(dst);
    }
}
