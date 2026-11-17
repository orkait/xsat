use crate::{
    cdcl::decide::Deciding,
    error::SolverError,
    options::{Opt, Options},
    solver::{idx, literal, negated, not, Lifecycle, Mode, Outcome, Propagation, Solver},
    store::{convert::widen, random::Generator, watch},
};

const ALWAYS_STABLE: i32 = 2;

const PORTED: [(Opt, i32); 1] = [(Opt::Fastel, 0)];

const SIMPLIFYING: [(Opt, i32); 2] = [(Opt::Factorstructural, 0), (Opt::Sweeprand, 0)];

#[must_use]
pub fn unported(options: &Options) -> Option<Opt> {
    let simplifying: &[(Opt, i32)] =
        if options.get(Opt::Simplify) == 0 && options.get(Opt::Preprocess) == 0 {
            &[]
        } else {
            &SIMPLIFYING
        };
    PORTED
        .iter()
        .chain(simplifying)
        .find(|&&(opt, value)| options.get(opt) != value)
        .map(|&(opt, _)| opt)
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Direction {
    Forward,
    Backward,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Sign {
    Positive,
    Negative,
}

impl Sign {
    fn of(lit: u32) -> Sign {
        if negated(lit) {
            Sign::Negative
        } else {
            Sign::Positive
        }
    }

    fn apply(self, lit: u32) -> u32 {
        match self {
            Sign::Positive => lit,
            Sign::Negative => not(lit),
        }
    }
}

impl Solver {
    pub fn solve(&mut self) -> Result<Outcome, SolverError> {
        self.start_solving()?;
        Ok(self.traced_run(&[]))
    }

    pub(crate) fn start_solving(&mut self) -> Result<(), SolverError> {
        self.input_closed()?;
        self.lifecycle = Lifecycle::Solved;
        self.restart_from_root();
        if !self.restoring.is_empty() {
            self.restore_clauses();
        }
        Ok(())
    }

    pub(crate) fn run(&mut self) -> Outcome {
        let first = self.statistics.searches == 0;
        let lucky = first && !self.assuming() && !self.connected();
        let mut res = None;
        if self.inconsistent {
            res = Some(Outcome::Unsatisfiable);
        }
        if res.is_none() && lucky && self.option(Opt::Luckyearly) != 0 {
            res = self.lucky();
        }
        if res.is_none() && first && self.preprocessing() {
            res = self.preprocess();
        }
        if res.is_none() && lucky && self.option(Opt::Luckylate) != 0 {
            res = self.lucky();
        }
        if res.is_none() && self.searching() {
            if first {
                self.start_search();
            }
            self.statistics.searches += 1;
            while res.is_none() {
                if let Some(conflict) = self.search_propagate() {
                    res = self.analyze(conflict);
                } else if let Some(clause) = self.external_clause() {
                    self.add_external_clause(clause.lits());
                    if self.inconsistent {
                        res = Some(Outcome::Unsatisfiable);
                    }
                } else if self.assignment.iterating {
                    self.assignment.iterating = false;
                } else if self.assignment.unassigned == 0 {
                    res = if self.assuming() {
                        self.decide_assumption()
                    } else {
                        Some(Outcome::Satisfiable)
                    };
                } else if self.terminated() {
                    break;
                } else if self.reducing() {
                    self.reduce();
                    if self.inconsistent {
                        res = Some(Outcome::Unsatisfiable);
                    }
                } else if self.switching_search_mode() {
                    self.switch_search_mode();
                } else if self.restarting() {
                    self.restart();
                } else if self.reordering() {
                    self.reorder();
                } else if self.rephasing() {
                    self.rephase();
                } else if self.probing_due() {
                    res = self.probe();
                } else if self.eliminating() {
                    self.eliminate();
                    if self.inconsistent {
                        res = Some(Outcome::Unsatisfiable);
                    }
                } else if self.conflict_limit_hit() || self.decision_limit_hit() {
                    break;
                } else if self.assuming() {
                    res = self.decide_assumption();
                } else {
                    self.decide(Deciding::Search);
                }
            }
            self.limits.conflicts = None;
            self.limits.decisions = None;
            self.reset_termination();
        }
        if res == Some(Outcome::Satisfiable) {
            self.extend();
        }
        res.unwrap_or(Outcome::Unknown)
    }

    pub fn limit_conflicts(&mut self, limit: u64) {
        self.limits.conflicts = Some(self.statistics.conflicts.saturating_add(limit));
    }

    pub fn limit_decisions(&mut self, limit: u64) {
        self.limits.decisions = Some(self.statistics.decisions.saturating_add(limit));
    }

    fn decision_limit_hit(&self) -> bool {
        self.limits
            .decisions
            .is_some_and(|limit| limit <= self.statistics.decisions)
    }

    fn conflict_limit_hit(&self) -> bool {
        self.limits
            .conflicts
            .is_some_and(|limit| limit <= self.statistics.conflicts)
    }

    fn searching(&self) -> bool {
        self.assignment.propagate != self.assignment.trail.len()
            || self.option(Opt::Probeinit) == 0
            || self.option(Opt::Eliminateinit) == 0
            || !self.conflict_limit_hit()
    }

    fn start_search(&mut self) {
        if self.option(Opt::Stable) == ALWAYS_STABLE {
            self.mode = Mode::Stable;
        }
        self.init_averages();
        self.classify();
        if self.mode == Mode::Stable {
            self.init_reluctant();
            self.update_scores();
        }
        self.init_tiers();
        self.init_limits();
        self.random = Generator(u64::from(self.option_u32(Opt::Seed)));
    }

    fn initial_limit(&self, opt: Opt) -> u64 {
        self.statistics.conflicts + u64::from(self.option_u32(opt))
    }

    fn init_limits(&mut self) {
        if self.option(Opt::Randec) != 0 {
            self.limits.randec = self.initial_limit(Opt::Randecinit);
        }
        if self.option(Opt::Reduce) != 0 {
            self.limits.reduce = self.initial_limit(Opt::Reduceinit);
        }
        if self.option(Opt::Reorder) != 0 {
            self.limits.reorder = self.initial_limit(Opt::Reorderinit);
        }
        if self.option(Opt::Rephase) != 0 {
            self.limits.rephase = self.initial_limit(Opt::Rephaseinit);
        }
        if self.mode == Mode::Focused {
            self.update_focused_restart_limit();
        }
        self.init_mode_limit();
        self.init_elimination_limits();
        self.init_probe_limit();
    }

    pub(crate) fn init_averages(&mut self) {
        let (slow, fast) = (self.option(Opt::Emaslow), self.option(Opt::Emafast));
        self.averages[self.mode.index()].init(slow, fast);
    }

    pub(crate) fn init_reluctant(&mut self) {
        if self.option(Opt::Reluctant) == 0 {
            self.reluctant.disable();
        } else {
            self.reluctant.enable(
                u64::from(self.option_u32(Opt::Reluctantint)),
                u64::from(self.option_u32(Opt::Reluctantlim)),
            );
        }
    }

    pub(crate) fn update_scores(&mut self) {
        for idx in 0..self.vars {
            if self.active[widen(idx)] && !self.scores.contains(idx) {
                self.scores.push(idx);
            }
        }
    }

    fn no_all_sign_clauses(&self, sign: Sign) -> bool {
        for at in self.clauses.arena.refs() {
            if self.clauses.last_irredundant.is_some_and(|last| last < at) {
                break;
            }
            if self.clauses.arena.redundant(at) || self.clauses.arena.garbage(at) {
                continue;
            }
            let covered = self
                .clauses
                .arena
                .lits(at)
                .iter()
                .any(|&lit| Sign::of(lit) != sign && self.value(lit) >= 0);
            if !covered {
                return false;
            }
        }
        for var in 0..self.vars {
            if !self.active[widen(var)] {
                continue;
            }
            for other in watch::binaries(&self.clauses.watches[widen(sign.apply(literal(var)))]) {
                if Sign::of(other) == sign && self.active[widen(idx(other))] {
                    return false;
                }
            }
        }
        true
    }

    fn assume_all(&mut self, sign: Sign) {
        for var in 0..self.vars {
            if !self.active[widen(var)] || self.value(literal(var)) != 0 {
                continue;
            }
            self.internal_assume(sign.apply(literal(var)));
            let _ = self.propagate(Propagation::Probing);
        }
    }

    fn lucky_direction(&mut self, direction: Direction, sign: Sign) -> Option<Outcome> {
        let eidxs = 0..self.imports.len();
        let order: Box<dyn Iterator<Item = usize>> = match direction {
            Direction::Forward => Box::new(eidxs),
            Direction::Backward => Box::new(eidxs.rev()),
        };
        for eidx in order {
            let Some(imported) = self.imports[eidx] else {
                continue;
            };
            if !self.active[widen(idx(imported))] || self.value(imported) != 0 {
                continue;
            }
            let lit = sign.apply(imported);
            self.internal_assume(lit);
            let Some(conflict) = self.propagate(Propagation::Probing) else {
                continue;
            };
            if self.assignment.level > 1 {
                self.backtrack_without_updating_phases(self.assignment.level - 1);
                self.internal_assume(not(lit));
                if self.propagate(Propagation::Probing).is_none() {
                    continue;
                }
                self.backtrack_without_updating_phases(0);
                return None;
            }
            let _ = self.analyze(conflict);
            if let Some(conflict) = self.propagate(Propagation::Probing) {
                let _ = self.analyze(conflict);
                return Some(Outcome::Unsatisfiable);
            }
        }
        Some(Outcome::Satisfiable)
    }

    fn lucky(&mut self) -> Option<Outcome> {
        if self.inconsistent || self.option(Opt::Lucky) == 0 {
            return None;
        }
        self.probing = true;
        let mut res = None;
        for (sign, assumed) in [
            (Sign::Negative, Sign::Positive),
            (Sign::Positive, Sign::Negative),
        ] {
            if res.is_none() && self.no_all_sign_clauses(sign) {
                self.assume_all(assumed);
                res = Some(Outcome::Satisfiable);
            }
        }
        let attempts = [
            (Direction::Forward, Sign::Negative),
            (Direction::Forward, Sign::Positive),
            (Direction::Backward, Sign::Negative),
            (Direction::Backward, Sign::Positive),
        ];
        for (direction, sign) in attempts {
            if res.is_none() {
                res = self.lucky_direction(direction, sign);
            }
        }
        self.probing = false;
        res
    }
}
