use crate::{
    inprocess::backbone::Order,
    options::Opt,
    solver::{idx, literal, not, Flush, Propagation, Solver, TRUE},
    store::{
        arena::{Ref, INITIAL_SEARCHED},
        convert::{narrow, real, truncate, widen},
        watch::{self, Head},
    },
    trace::proof::Step,
};

const DONE: u32 = u32::MAX;
const PER_MILLE: f64 = 1e-3;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Effort {
    Bounded,
    Complete,
}

#[derive(Clone, Copy, Debug)]
enum Work {
    Visit(u32),
    Leave(u32),
}

impl Solver {
    pub(crate) fn assign_and_propagate_units(&mut self, units: &mut Vec<u32>) {
        while !self.inconsistent {
            let Some(unit) = units.pop() else {
                break;
            };
            let value = self.value(unit);
            if value < 0 {
                self.proof_lits(Step::Add, &[]);
                self.inconsistent = true;
            } else if value == 0 {
                self.learned_unit(unit);
                let _ = self.propagate_trail(Propagation::Probing, None, Flush::Keep);
            }
        }
    }

    fn implied(&self, lit: u32, ticks: &mut u64) -> impl Iterator<Item = u32> + '_ {
        let watches = &self.clauses.watches[widen(not(lit))];
        *ticks += 1 + watch::cache_lines(watches.len());
        watch::binaries(watches).filter(|&other| self.active[widen(idx(other))])
    }

    fn determine_representatives(&mut self, ticks: &mut u64) -> Vec<u32> {
        let lits = 2 * widen(self.vars);
        let mut repr = vec![None; lits];
        let mut mark = vec![0_u32; lits];
        let mut reach = vec![0_u32; lits];
        let mut reached = 0;
        let mut scc = Vec::new();
        let mut work = Vec::new();
        let mut units = Vec::new();
        let mut inconsistent = false;
        for root in 0..narrow(lits) {
            if inconsistent {
                break;
            }
            if mark[widen(root)] != 0 || !self.active[widen(idx(root))] {
                continue;
            }
            work.push(Work::Visit(root));
            let mut failed = false;
            let mark_root = reached + 1;
            while !inconsistent {
                let Some(&top) = work.last() else {
                    break;
                };
                match top {
                    Work::Leave(lit) => {
                        let _ = work.pop();
                        let mark_lit = mark[widen(lit)];
                        let mut reach_lit = reach[widen(lit)];
                        for other in self.implied(lit, ticks) {
                            reach_lit = reach_lit.min(reach[widen(other)]);
                        }
                        if reach_lit != mark_lit {
                            reach[widen(lit)] = reach_lit;
                            continue;
                        }
                        let mut begin = scc.len();
                        while begin > 0 {
                            begin -= 1;
                            if scc[begin] == lit {
                                break;
                            }
                        }
                        let min_lit = scc[begin..].iter().copied().min().unwrap_or(lit);
                        for &other in &scc[begin..] {
                            repr[widen(other)] = Some(min_lit);
                            reach[widen(other)] = DONE;
                            let Some(repr_not_other) = repr[widen(not(other))] else {
                                continue;
                            };
                            if min_lit == repr_not_other {
                                units.push(min_lit);
                                inconsistent = true;
                                break;
                            }
                            if failed || mark_root > mark[widen(not(other))] {
                                continue;
                            }
                            units.push(not(root));
                            failed = true;
                        }
                        scc.truncate(begin);
                    }
                    Work::Visit(lit) if mark[widen(lit)] == 0 => {
                        let _ = work.pop();
                        work.push(Work::Leave(lit));
                        scc.push(lit);
                        reached += 1;
                        mark[widen(lit)] = reached;
                        reach[widen(lit)] = reached;
                        for other in self.implied(lit, ticks) {
                            if mark[widen(other)] == 0 {
                                work.push(Work::Visit(other));
                            }
                        }
                    }
                    Work::Visit(_) => {
                        let _ = work.pop();
                    }
                }
            }
        }
        self.assign_and_propagate_units(&mut units);
        (0..narrow(lits))
            .map(|lit| {
                if self.frozen_variable(idx(lit)) {
                    lit
                } else {
                    repr[widen(lit)].unwrap_or(lit)
                }
            })
            .collect()
    }

    fn representative_equivalences(&self, repr: &[u32]) -> Vec<u32> {
        (0..self.vars)
            .filter(|&idx| {
                let lit = literal(idx);
                self.active[widen(idx)] && repr[widen(lit)] != lit
            })
            .collect()
    }

    fn trace_representative_equivalences(&mut self, repr: &[u32], eliminate: &[u32], step: Step) {
        for &idx in eliminate {
            let lit = literal(idx);
            let other = repr[widen(lit)];
            self.proof_lits(step, &[not(lit), other]);
            self.proof_lits(step, &[lit, not(other)]);
        }
    }

    fn remove_representative_equivalences(&mut self, repr: &[u32], eliminate: &[u32]) {
        for &idx in eliminate {
            let lit = literal(idx);
            let other = repr[widen(lit)];
            self.trace_representative_equivalences(repr, &[idx], Step::Delete);
            self.mark_eliminated_variable(idx);
            let other_value = self.value(other);
            if other_value <= 0 {
                self.weaken_binary(not(lit), other);
            }
            if other_value >= 0 {
                self.weaken_binary(lit, not(other));
            }
        }
    }

    fn substitute_binaries(&mut self, repr: &[u32]) {
        let mut units = Vec::new();
        let mut deleted = Vec::new();
        let mut removed = Vec::new();
        let mut delayed = Vec::new();
        for lit in 0..2 * self.vars {
            let repr_lit = repr[widen(lit)];
            let not_repr_lit = not(repr_lit);
            let mut watches = std::mem::take(&mut self.clauses.watches[widen(lit)]);
            let (mut p, mut q) = (0, 0);
            while p < watches.len() {
                let head = watches[p];
                p += 1;
                let Head::Binary(other) = watch::decode(head) else {
                    p += 1;
                    continue;
                };
                let repr_other = repr[widen(other)];
                if repr_other == not_repr_lit {
                    if lit < other {
                        deleted.push([lit, other]);
                    }
                } else if repr_other == repr_lit {
                    if lit < other {
                        units.push(repr_lit);
                        deleted.push([lit, other]);
                    }
                } else {
                    if (lit != repr_lit || other != repr_other) && lit < other {
                        self.proof_lits(Step::Add, &[repr_lit, repr_other]);
                        removed.push([lit, other]);
                    }
                    if lit == repr_lit {
                        watches[q] = watch::binary(repr_other);
                        q += 1;
                    } else {
                        delayed.push(watch::binary(repr_other));
                    }
                }
            }
            watches.truncate(q);
            self.clauses.watches[widen(lit)] = watches;
            if lit != repr_lit {
                self.clauses.watches[widen(repr_lit)].append(&mut delayed);
            }
        }
        self.assign_and_propagate_units(&mut units);
        for [lit, other] in deleted {
            self.delete_binary(lit, other);
        }
        for pair in removed {
            self.proof_lits(Step::Delete, &pair);
        }
    }

    fn substitute_clauses(&mut self, repr: &[u32]) {
        let mut units = Vec::new();
        let mut delayed_garbage = Vec::new();
        let mut next = Ref(0);
        while next < self.clauses.arena.end() {
            let at = next;
            next = self.clauses.arena.next(at);
            if self.clauses.arena.garbage(at) {
                continue;
            }
            let mut shrink = false;
            let mut satisfied = false;
            let mut substitute = false;
            let mut tautological = false;
            for position in 0..self.clauses.arena.size(at) {
                let lit = self.clauses.arena.lit(at, position);
                let lit_value = self.value(lit);
                if lit_value < 0 {
                    shrink = true;
                    continue;
                }
                if lit_value > 0 {
                    satisfied = true;
                    break;
                }
                let repr_lit = repr[widen(lit)];
                let repr_value = self.value(repr_lit);
                if repr_value < 0 {
                    shrink = true;
                    continue;
                }
                if repr_value > 0 {
                    satisfied = true;
                    break;
                }
                if lit != repr_lit {
                    substitute = true;
                }
                if self.marks[widen(repr_lit)] != 0 {
                    shrink = true;
                    continue;
                }
                if self.marks[widen(not(repr_lit))] != 0 {
                    tautological = true;
                    break;
                }
                self.marks[widen(repr_lit)] = TRUE;
                self.clause.push(repr_lit);
            }
            if satisfied || tautological {
                self.mark_clause_as_garbage(at);
            } else if substitute || shrink {
                match *self.clause.as_slice() {
                    [] => {
                        self.proof_lits(Step::Add, &[]);
                        self.inconsistent = true;
                        break;
                    }
                    [unit] => {
                        units.push(unit);
                        delayed_garbage.push(at);
                    }
                    [first, second] => {
                        self.new_binary_clause(first, second);
                        self.mark_clause_as_garbage(at);
                    }
                    _ => {
                        self.proof_replace_clause(at);
                        let size = narrow(self.clause.len());
                        self.clauses.arena.lits_mut(at)[..self.clause.len()]
                            .copy_from_slice(&self.clause);
                        if size < self.clauses.arena.size(at) {
                            self.clauses.arena.shrink(at, size);
                            self.clauses.arena.set_searched(at, INITIAL_SEARCHED);
                        }
                    }
                }
            }
            for position in 0..self.clause.len() {
                self.marks[widen(self.clause[position])] = 0;
            }
            self.clause.clear();
        }
        self.assign_and_propagate_units(&mut units);
        for at in delayed_garbage {
            self.mark_clause_as_garbage(at);
        }
    }

    fn substitute_round(&mut self, ticks: &mut u64) -> bool {
        let active = self.active_count;
        let repr = self.determine_representatives(ticks);
        let eliminate = if self.inconsistent {
            Vec::new()
        } else {
            self.representative_equivalences(&repr)
        };
        self.trace_representative_equivalences(&repr, &eliminate, Step::Add);
        if !self.inconsistent {
            self.substitute_binaries(&repr);
        }
        if !self.inconsistent {
            self.substitute_clauses(&repr);
        }
        if !self.inconsistent {
            self.remove_representative_equivalences(&repr, &eliminate);
        }
        !self.inconsistent && active != self.active_count
    }

    pub(crate) fn substitute(&mut self, effort: Effort) {
        if self.inconsistent {
            return;
        }
        self.clauses.order = Order::Mixed;
        if self.option(Opt::Substitute) == 0 || self.terminated() {
            return;
        }
        let mut ticks = 0;
        for _ in 0..self.option_u32(Opt::Substituterounds) {
            let before = ticks;
            if !self.substitute_round(&mut ticks) {
                break;
            }
            if effort == Effort::Complete {
                continue;
            }
            let reference = self.statistics.search_ticks - self.last.probe_ticks;
            let fraction = f64::from(self.option(Opt::Substituteeffort)) * PER_MILLE;
            if ticks - before > truncate(fraction * real(reference)) {
                break;
            }
        }
        if !self.inconsistent {
            self.watch_large_clauses(Ref(0));
            self.clauses.order = Order::BinariesFirst;
            self.assignment.propagate = 0;
            let _ = self.propagate_trail(Propagation::Probing, None, Flush::Trail);
        }
    }
}
