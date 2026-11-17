use crate::{
    cdcl::kimits::nlogpown,
    inprocess::{dense::Rewatch, kitten::Kitten},
    options::Opt,
    solver::{idx, literal, not, Mode, Solver},
    store::{
        arena::{Ref, INVALID_LIT},
        convert::{real, truncate, widen},
        flags::Flag,
        heap::Heap,
        watch::{self, Occurrence},
    },
    trace::proof::Step,
};

const ELIMINATE_EXPONENT: u32 = 2;

#[derive(Debug, Default)]
pub(crate) struct Elimination {
    enabled: bool,
    conflicts: u64,
    variables_eliminate: u64,
    variables_subsume: u64,
    pub(crate) bound: u32,
    pub(crate) last_ticks: u64,
    schedule: Option<Heap>,
    pub(crate) resolvents: Vec<u32>,
    pub(crate) gates: [Vec<u32>; 2],
    pub(crate) antecedents: [Vec<u32>; 2],
    pub(crate) resolve_gate: bool,
}

impl Solver {
    pub(crate) fn init_elimination_limits(&mut self) {
        let enabled = self.option(Opt::Simplify) != 0 && self.option(Opt::Eliminate) != 0;
        self.elimination.enabled = enabled;
        if enabled {
            let delta = u64::from(self.option_u32(Opt::Eliminateinit));
            self.elimination.conflicts = self.statistics.conflicts + self.scale_delta(delta);
            self.elimination.bound = 0;
        }
    }

    pub(crate) fn eliminating(&self) -> bool {
        let elimination = &self.elimination;
        let statistics = &self.statistics;
        elimination.enabled
            && statistics.clauses_irredundant > 0
            && self.last.reduce != statistics.conflicts
            && elimination.conflicts <= statistics.conflicts
            && (elimination.variables_eliminate < statistics.variables_eliminate
                || elimination.variables_subsume < statistics.variables_subsume)
    }

    fn variable_score(&self, idx: u32) -> f64 {
        let lit = literal(idx);
        let occlim = widen(self.option_u32(Opt::Eliminateocclim));
        let pos = self.clauses.watches[widen(lit)].len().min(occlim);
        let neg = self.clauses.watches[widen(not(lit))].len().min(occlim);
        let count = |value: usize| real(u64::try_from(value).unwrap_or(u64::MAX));
        let prod = count(pos * neg);
        let sum = count(pos + neg);
        let occlim2 = count(occlim) * count(occlim);
        let score = prod - sum;
        let relevancy = match self.mode {
            Mode::Stable => self.scores.score(idx),
            Mode::Focused => f64::from(self.queue.links[widen(idx)].stamp),
        };
        relevancy + score - occlim2
    }

    pub(crate) fn update_variable_score(&mut self, idx: u32) {
        let score = self.variable_score(idx);
        if let Some(schedule) = &mut self.elimination.schedule {
            schedule.update(idx, -score);
        }
    }

    fn update_after_removing_variable(&mut self, idx: u32) {
        if self.elimination.schedule.is_none() || self.flags[widen(idx)].has(Flag::Fixed) {
            return;
        }
        self.update_variable_score(idx);
        if let Some(schedule) = &mut self.elimination.schedule {
            if !schedule.contains(idx) {
                schedule.push(idx);
            }
        }
    }

    pub(crate) fn eliminate_binary(&mut self, lit: u32, other: u32) {
        self.eagerly_remove_watch(other, watch::binary(lit));
        self.delete_binary(lit, other);
        self.update_after_removing_variable(idx(other));
    }

    pub(crate) fn eliminate_clause(&mut self, at: Ref, except: u32) {
        self.mark_clause_as_garbage(at);
        if self.elimination.schedule.is_none() {
            return;
        }
        for position in 0..self.clauses.arena.size(at) {
            let lit = self.clauses.arena.lit(at, position);
            if lit != except {
                self.update_after_removing_variable(idx(lit));
            }
        }
    }

    fn schedule_variables(&mut self) {
        self.elimination.schedule = Some(Heap::default());
        for idx in 0..self.vars {
            if self.can_eliminate_variable(idx) {
                self.update_after_removing_variable(idx);
            }
        }
    }

    pub(crate) fn flush_units_while_connected(&mut self) {
        let propagate = self.assignment.propagate;
        if propagate == self.assignment.trail.len() || !self.dense_propagate() {
            return;
        }
        for position in propagate..self.assignment.trail.len() {
            let unit = self.assignment.trail[position];
            let mut watches = std::mem::take(&mut self.clauses.watches[widen(unit)]);
            let mut kept = 0;
            for position in 0..watches.len() {
                let word = watches[position];
                match watch::occurrence(word) {
                    Occurrence::Binary(other) => {
                        watches[kept] = word;
                        kept += 1;
                        if self.value(other) == 0 {
                            self.update_after_removing_variable(idx(other));
                        }
                    }
                    Occurrence::Large(at) => {
                        if !self.clauses.arena.garbage(at) {
                            self.eliminate_clause(at, unit);
                        }
                    }
                }
            }
            watches.truncate(kept);
            self.clauses.watches[widen(unit)] = watches;
        }
    }

    fn connect_resolvents(&mut self) {
        let resolvents = std::mem::take(&mut self.elimination.resolvents);
        let mut satisfied = false;
        for &other in &resolvents {
            if other == INVALID_LIT {
                if satisfied {
                    satisfied = false;
                } else {
                    match *self.clause.as_slice() {
                        [] => {
                            self.proof_lits(Step::Add, &[]);
                            self.inconsistent = true;
                            break;
                        }
                        [unit] => self.learned_unit(unit),
                        _ => {
                            let _ = self.new_irredundant_clause();
                            for position in 0..self.clause.len() {
                                self.update_variable_score(idx(self.clause[position]));
                            }
                        }
                    }
                }
                self.clause.clear();
            } else if !satisfied {
                let value = self.value(other);
                if value > 0 {
                    satisfied = true;
                } else if value == 0 {
                    self.clause.push(other);
                }
            }
        }
        self.clause.clear();
    }

    fn weaken_clauses(&mut self, lit: u32) {
        let not_lit = not(lit);
        let positive = std::mem::take(&mut self.clauses.watches[widen(lit)]);
        for word in positive {
            match watch::occurrence(word) {
                Occurrence::Binary(other) => {
                    if self.value(other) <= 0 {
                        self.weaken_binary(lit, other);
                    }
                    self.eliminate_binary(lit, other);
                }
                Occurrence::Large(at) => {
                    if self.clauses.arena.garbage(at) {
                        continue;
                    }
                    if !self.satisfied(at) {
                        self.weaken_clause(lit, at);
                    }
                    self.eliminate_clause(at, lit);
                }
            }
        }
        let negative = std::mem::take(&mut self.clauses.watches[widen(not_lit)]);
        for word in negative {
            match watch::occurrence(word) {
                Occurrence::Binary(other) => {
                    if self.value(other) <= 0 {
                        self.weaken_binary(not_lit, other);
                    }
                    self.eliminate_binary(not_lit, other);
                }
                Occurrence::Large(at) => {
                    if self.clauses.arena.garbage(at) {
                        continue;
                    }
                    if !self.satisfied(at) {
                        self.weaken_clause(not_lit, at);
                    }
                    self.eliminate_clause(at, not_lit);
                }
            }
        }
        self.flush_units_while_connected();
    }

    fn satisfied(&self, at: Ref) -> bool {
        self.clauses
            .arena
            .lits(at)
            .iter()
            .any(|&lit| self.value(lit) > 0)
    }

    fn next_elimination_bound(&mut self) {
        let max_bound = self.option_u32(Opt::Eliminatebound);
        let current = self.elimination.bound;
        if current == max_bound {
            self.elimination.variables_eliminate = self.statistics.variables_eliminate;
            self.elimination.variables_subsume = self.statistics.variables_subsume;
        } else {
            self.elimination.bound = if current == 0 {
                1
            } else {
                (2 * current).min(max_bound)
            };
            for flags in &mut self.flags {
                flags.set(Flag::Eliminate);
            }
            self.elimination.variables_eliminate = 0;
        }
    }

    fn can_eliminate_variable(&self, idx: u32) -> bool {
        self.active[widen(idx)]
            && self.flags[widen(idx)].has(Flag::Eliminate)
            && !self.frozen_variable(idx)
    }

    fn eliminate_variable(&mut self, idx: u32) -> bool {
        self.flags[widen(idx)].clear(Flag::Eliminate);
        let Some(lit) = self.generate_resolvents(idx) else {
            return false;
        };
        self.connect_resolvents();
        if !self.inconsistent {
            self.weaken_clauses(lit);
        }
        self.mark_eliminated_variable(idx);
        true
    }

    fn eliminate_variables(&mut self) {
        let resolution_limit =
            self.effort_limit(Opt::Eliminateeffort, self.statistics.eliminate_resolutions);
        let forward = self.option(Opt::Forward) != 0;
        let rounds = self.option(Opt::Eliminaterounds);
        let mut round = 0;
        loop {
            round += 1;
            let mut complete = true;
            if forward {
                let propagate = self.assignment.propagate;
                complete = self.forward_subsume_during_elimination();
                if self.inconsistent {
                    break;
                }
                self.flush_large_connected();
                self.connect_irredundant_large_clauses();
                self.assignment.propagate = propagate;
                self.flush_units_while_connected();
                if self.inconsistent {
                    break;
                }
            } else {
                self.connect_irredundant_large_clauses();
            }
            self.schedule_variables();
            let mut eliminated = 0;
            while !self.inconsistent {
                let Some(schedule) = self
                    .elimination
                    .schedule
                    .as_mut()
                    .filter(|schedule| !schedule.is_empty())
                else {
                    break;
                };
                if self.terminator.terminated() {
                    complete = false;
                    break;
                }
                let idx = schedule.pop_max();
                if !self.can_eliminate_variable(idx) {
                    continue;
                }
                if self.statistics.eliminate_resolutions > resolution_limit {
                    complete = false;
                    break;
                }
                if self.eliminate_variable(idx) {
                    eliminated += 1;
                }
                if self.inconsistent {
                    break;
                }
                self.flush_units_while_connected();
            }
            if eliminated > 0 {
                complete = false;
            }
            if !self.inconsistent {
                self.flush_large_connected();
                self.dense_collect();
            }
            if self.inconsistent {
                break;
            }
            self.elimination.schedule = None;
            if complete
                || round == rounds
                || self.statistics.eliminate_resolutions > resolution_limit
                || self.terminated()
            {
                break;
            }
        }
        let remain = self
            .elimination
            .schedule
            .take()
            .is_some_and(|schedule| !schedule.is_empty());
        if !self.inconsistent {
            if remain {
                for flags in &mut self.flags {
                    flags.clear(Flag::Eliminate);
                }
            } else {
                self.next_elimination_bound();
            }
        }
    }

    fn run_elimination(&mut self) {
        self.backtrack_propagate_and_flush_trail();
        if self.option(Opt::Definitions) != 0 {
            self.kitten = Some(Kitten::new(self.statistics.kitten_ticks, self.terminator()));
        }
        self.enter_dense_mode(None);
        self.eliminate_variables();
        self.resume_sparse_mode(Rewatch::FlushEliminated, &[]);
        if let Some(kitten) = self.kitten.take() {
            self.statistics.kitten_ticks = kitten.ticks();
        }
    }

    pub(crate) fn eliminate(&mut self) {
        self.statistics.eliminations += 1;
        self.run_elimination();
        self.classify();
        if !self.inconsistent {
            let delta = real(u64::from(self.option_u32(Opt::Eliminateint)));
            let scaled =
                truncate(delta * nlogpown(self.statistics.eliminations, ELIMINATE_EXPONENT));
            self.elimination.conflicts = self.statistics.conflicts + self.scale_delta(scaled);
        }
        self.elimination.last_ticks = self.statistics.search_ticks;
    }
}
