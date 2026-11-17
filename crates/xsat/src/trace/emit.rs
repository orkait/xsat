use crate::{
    error::SolverError,
    options::Opt,
    solver::{idx, Lifecycle, Solver},
    store::{arena::Ref, convert::widen},
    trace::proof::{Conclusion, Proof, Step},
};

impl Solver {
    pub fn trace_proof(&mut self, mut proof: Proof) -> Result<(), SolverError> {
        if self.propagator.is_some() {
            return Err(SolverError::PropagatorWithProof);
        }
        if self.proof.is_some() || self.lifecycle != Lifecycle::Fresh {
            return Err(SolverError::ProofAfterInput);
        }
        if self.option(Opt::Flushproof) != 0 {
            proof.flush_every_line();
        }
        self.proof = Some(proof);
        Ok(())
    }

    pub(crate) fn tracing_drat(&self) -> bool {
        self.proof
            .as_ref()
            .is_some_and(|proof| !proof.incremental())
    }

    pub fn take_proof(&mut self) -> Option<Proof> {
        self.proof.take()
    }

    fn with_proof(&mut self, write: impl FnOnce(&mut Proof, &Solver)) {
        let Some(mut proof) = self.proof.take() else {
            return;
        };
        write(&mut proof, self);
        self.proof = Some(proof);
    }

    fn proof_line(&mut self, step: Step, lits: impl IntoIterator<Item = u32>) {
        self.with_proof(|proof, solver| {
            proof.line(step, lits.into_iter().map(|lit| solver.export_literal(lit)));
        });
    }

    pub(crate) fn proof_lits(&mut self, step: Step, lits: &[u32]) {
        if self.proof.is_some() {
            self.proof_line(step, lits.iter().copied());
        }
    }

    pub(crate) fn proof_clause(&mut self, step: Step, at: Ref) {
        self.with_proof(|proof, solver| {
            let lits = solver.clauses.arena.lits(at).iter();
            proof.line(step, lits.map(|&lit| solver.export_literal(lit)));
        });
    }

    pub(crate) fn proof_replace_clause(&mut self, at: Ref) {
        self.with_proof(|proof, solver| {
            let lits = solver.clause.iter();
            proof.line(Step::Add, lits.map(|&lit| solver.export_literal(lit)));
        });
        self.proof_clause(Step::Delete, at);
    }

    pub(crate) fn proof_external(&mut self, step: Step, elits: &[i32]) {
        if let Some(proof) = &mut self.proof {
            proof.line(step, elits.iter().copied());
        }
    }

    pub(crate) fn proof_conclude(&mut self, conclusion: Conclusion<'_>) {
        if let Some(proof) = &mut self.proof {
            proof.conclude(conclusion);
        }
    }

    pub(crate) fn proof_shrink_clause(&mut self, at: Ref, remove: u32, keep: u32) {
        self.with_proof(|proof, solver| {
            let kept = solver
                .clauses
                .arena
                .lits(at)
                .iter()
                .copied()
                .filter(|&lit| {
                    lit != remove
                        && (lit == keep
                            || solver.assignment.values[widen(lit)] >= 0
                            || solver.assignment.assigned[widen(idx(lit))].level != 0)
                });
            proof.line(Step::Add, kept.map(|lit| solver.export_literal(lit)));
        });
        self.proof_clause(Step::Delete, at);
    }
}
