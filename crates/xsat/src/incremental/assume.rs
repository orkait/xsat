use crate::{
    error::SolverError,
    solver::{checked_literal, idx, not, Frame, Outcome, Reason, Solver},
    store::convert::{narrow, widen},
    trace::proof::Conclusion,
};

#[derive(Debug, Default)]
pub(crate) struct Assumptions {
    lits: Vec<i32>,
    core: Vec<i32>,
    frozen: Vec<u32>,
}

impl Solver {
    pub fn solve_assuming(&mut self, assumptions: &[i32]) -> Result<Outcome, SolverError> {
        for &elit in assumptions {
            checked_literal(elit)?;
        }
        if !assumptions.is_empty() && self.tracing_drat() {
            return Err(SolverError::AssumptionsNeedIdrup);
        }
        self.start_solving()?;
        for &elit in assumptions {
            self.import_frozen(elit);
        }
        self.restore_clauses();
        assumptions.clone_into(&mut self.assumptions.lits);
        let outcome = self.traced_run(assumptions);
        for &elit in assumptions {
            self.melt(elit);
        }
        self.assumptions.lits.clear();
        Ok(outcome)
    }

    #[must_use]
    pub fn core(&self) -> &[i32] {
        &self.assumptions.core
    }

    pub fn freeze(&mut self, elit: i32) -> Result<(), SolverError> {
        checked_literal(elit)?;
        self.freeze_external(elit);
        Ok(())
    }

    pub(crate) fn import_frozen(&mut self, elit: i32) {
        self.claim_variable(elit);
        let ilit = self.import(elit);
        if self.fixed(ilit) == 0 {
            self.activate_literal(ilit);
        }
        self.freeze_external(elit);
    }

    pub(crate) fn freeze_external(&mut self, elit: i32) {
        let eidx = widen(elit.unsigned_abs());
        if self.assumptions.frozen.len() <= eidx {
            self.assumptions.frozen.resize(eidx + 1, 0);
        }
        self.assumptions.frozen[eidx] += 1;
    }

    pub fn melt(&mut self, elit: i32) {
        if let Some(count) = self.assumptions.frozen.get_mut(widen(elit.unsigned_abs())) {
            *count = count.saturating_sub(1);
        }
    }

    pub(crate) fn frozen_variable(&self, idx: u32) -> bool {
        let eidx = widen(self.exports[widen(idx)]);
        eidx != 0
            && self
                .assumptions
                .frozen
                .get(eidx)
                .is_some_and(|&count| count > 0)
    }

    pub(crate) fn assuming(&self) -> bool {
        widen(self.assignment.level) < self.assumptions.lits.len()
    }

    pub(crate) fn decide_assumption(&mut self) -> Option<Outcome> {
        let elit = self.assumptions.lits[widen(self.assignment.level)];
        let Some(Some(ilit)) = self.imports.get(widen(elit.unsigned_abs())).copied() else {
            return Some(Outcome::Unknown);
        };
        let lit = if elit < 0 { not(ilit) } else { ilit };
        match self.value(lit) {
            0 => {
                self.internal_assume(lit);
                None
            }
            value if value > 0 => {
                self.assignment.level += 1;
                self.assignment.frames.push(Frame {
                    decision: None,
                    trail: narrow(self.assignment.trail.len()),
                    used: 0,
                    promote: false,
                });
                None
            }
            _ => {
                self.failing(elit, lit);
                Some(Outcome::Unsatisfiable)
            }
        }
    }

    fn failing(&mut self, elit: i32, lit: u32) {
        let mut core = vec![elit];
        if self.level_of(lit) > 0 {
            self.push_analyzed(idx(lit));
            for position in (0..self.assignment.trail.len()).rev() {
                let implied = self.assignment.trail[position];
                let assigned = self.assignment.assigned[widen(idx(implied))];
                if !assigned.analyzed {
                    continue;
                }
                match assigned.reason() {
                    Reason::Decision => core.push(self.export_literal(implied)),
                    Reason::Unit => {}
                    Reason::Binary(other) => self.analyze_reason_literal(other),
                    Reason::Clause(at) => {
                        for position in 0..self.clauses.arena.size(at) {
                            let other = self.clauses.arena.lit(at, position);
                            if other != implied {
                                self.analyze_reason_literal(other);
                            }
                        }
                    }
                }
            }
            self.clear_analyzed();
        }
        self.assumptions.core = core;
    }

    fn analyze_reason_literal(&mut self, lit: u32) {
        let idx = idx(lit);
        if self.level_of(lit) > 0 && !self.assignment.assigned[widen(idx)].analyzed {
            self.push_analyzed(idx);
        }
    }

    pub(crate) fn restart_from_root(&mut self) {
        self.assumptions.core.clear();
        self.backtrack_without_updating_phases(0);
    }
}

impl Solver {
    pub(crate) fn traced_run(&mut self, assumptions: &[i32]) -> Outcome {
        self.proof_conclude(Conclusion::Query(assumptions));
        let outcome = self.run();
        if self.proof.is_some() {
            match outcome {
                Outcome::Satisfiable => {
                    let model: Vec<i32> = (1..narrow(self.imports.len()))
                        .filter(|&eidx| !self.extension.get(widen(eidx)).copied().unwrap_or(false))
                        .filter_map(|eidx| i32::try_from(eidx).ok())
                        .map(|elit| match self.external_value(elit) {
                            0 => elit,
                            value => value,
                        })
                        .collect();
                    self.proof_conclude(Conclusion::Satisfiable(&model));
                }
                Outcome::Unsatisfiable => {
                    let core = self.assumptions.core.clone();
                    self.proof_conclude(Conclusion::Unsatisfiable(&core));
                }
                Outcome::Unknown => self.proof_conclude(Conclusion::Unknown),
            }
        }
        outcome
    }
}
