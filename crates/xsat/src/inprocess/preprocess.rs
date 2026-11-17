use crate::{
    cdcl::reduce::Mapping,
    options::Opt,
    solver::{Outcome, Propagation, Solver},
    store::arena::Ref,
};

impl Solver {
    pub(crate) fn preprocessing(&self) -> bool {
        self.option(Opt::Preprocess) != 0
            && self.option(Opt::Probe) != 0
            && self.option(Opt::Preprocessprobe) != 0
    }

    fn initially_propagate(&mut self) -> bool {
        let conflict = self.propagate(Propagation::Initially);
        if let Some(conflict) = conflict {
            let _ = self.analyze(conflict);
        }
        conflict.is_none()
    }

    fn binary_and_irredundant_clauses(&self) -> u64 {
        self.statistics.clauses_binary + self.statistics.clauses_irredundant
    }

    pub(crate) fn preprocess(&mut self) -> Option<Outcome> {
        if !self.initially_propagate() {
            return Some(Outcome::Unsatisfiable);
        }
        if !self.units.is_empty() {
            let mapping = if self.option(Opt::Compact) == 0 {
                Mapping::Identity
            } else {
                Mapping::Compacting
            };
            self.sparse_collect(mapping, Ref(0));
        }
        let rounds = self.option_u32(Opt::Preprocessrounds);
        for round in 1..=rounds {
            if self.inconsistent || self.terminated() {
                break;
            }
            let variables = self.active_count;
            let clauses = self.binary_and_irredundant_clauses();
            self.probe_initially();
            if round == rounds
                || variables == self.active_count
                    && clauses == self.binary_and_irredundant_clauses()
            {
                break;
            }
        }
        self.inconsistent.then_some(Outcome::Unsatisfiable)
    }
}
