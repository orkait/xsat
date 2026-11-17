use std::cmp::Reverse;

use crate::{
    error::SolverError,
    solver::{checked_literal, not, Reason, Solver},
    store::{arena::Kind, convert::widen},
};

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ExternalClause(Vec<i32>);

impl ExternalClause {
    pub fn new(lits: Vec<i32>) -> Result<ExternalClause, SolverError> {
        for &lit in &lits {
            checked_literal(lit)?;
        }
        Ok(ExternalClause(lits))
    }

    pub(crate) fn from_checked(lits: Vec<i32>) -> ExternalClause {
        ExternalClause(lits)
    }

    #[must_use]
    pub fn lits(&self) -> &[i32] {
        &self.0
    }
}

pub trait Propagator: std::fmt::Debug + Send {
    fn observed(&self) -> Vec<i32>;
    fn propagate(&mut self, solver: &Solver) -> Option<ExternalClause>;
}

impl Solver {
    pub fn connect(&mut self, propagator: Box<dyn Propagator>) -> Result<(), SolverError> {
        self.input_closed()?;
        if self.proof.is_some() {
            return Err(SolverError::PropagatorWithProof);
        }
        let observed = propagator.observed();
        for &elit in &observed {
            checked_literal(elit)?;
        }
        let _ = self.disconnect();
        self.restart_from_root();
        for elit in observed {
            self.import_frozen(elit);
        }
        self.restore_clauses();
        self.propagator = Some(propagator);
        Ok(())
    }

    pub fn disconnect(&mut self) -> Option<Box<dyn Propagator>> {
        let propagator = self.propagator.take()?;
        for elit in propagator.observed() {
            self.melt(elit);
        }
        Some(propagator)
    }

    pub(crate) fn connected(&self) -> bool {
        self.propagator.is_some()
    }

    pub(crate) fn external_clause(&mut self) -> Option<ExternalClause> {
        let mut propagator = self.propagator.take()?;
        let clause = propagator.propagate(self);
        self.propagator = Some(propagator);
        clause
    }

    pub(crate) fn add_external_clause(&mut self, elits: &[i32]) {
        let mut lits: Vec<u32> = Vec::new();
        for &elit in elits {
            let Some(Some(ilit)) = self.imports.get(widen(elit.unsigned_abs())).copied() else {
                for &elit in elits {
                    self.add_external(elit);
                }
                self.add_external(0);
                return;
            };
            let lit = if elit < 0 { not(ilit) } else { ilit };
            if lits.contains(&not(lit)) {
                return;
            }
            if !lits.contains(&lit) {
                lits.push(lit);
            }
        }
        for &lit in &lits {
            if self.fixed(lit) == 0 {
                self.activate_literal(lit);
            }
        }
        lits.sort_by_key(|&lit| match self.value(lit) {
            value if value > 0 => (0, Reverse(0)),
            0 => (1, Reverse(0)),
            _ => (2, Reverse(self.level_of(lit))),
        });
        match *lits.as_slice() {
            [] => self.inconsistent = true,
            [unit] => {
                self.backtrack_without_updating_phases(0);
                match self.value(unit) {
                    0 => self.assign(0, unit, Reason::Unit),
                    value if value < 0 => self.inconsistent = true,
                    _ => {}
                }
            }
            [first, second, ..] => self.attach_external_clause(lits, first, second),
        }
    }

    fn attach_external_clause(&mut self, lits: Vec<u32>, first: u32, second: u32) {
        let (first_value, second_value) = (self.value(first), self.value(second));
        let (first_level, second_level) = (self.level_of(first), self.level_of(second));
        let implied = if second_value >= 0 || (first_value > 0 && first_level <= second_level) {
            false
        } else if first_value < 0 && first_level == 0 {
            self.inconsistent = true;
            return;
        } else if first_value < 0 && first_level == second_level {
            self.backtrack_without_updating_phases(first_level - 1);
            false
        } else {
            self.backtrack_without_updating_phases(second_level);
            true
        };
        self.clause = lits;
        let at = self.new_clause(Kind::Irredundant, 0);
        self.clause.clear();
        if implied {
            match at {
                Some(at) => self.assign_reference(first, at),
                None => self.assign_binary(first, second),
            }
        }
    }
}
