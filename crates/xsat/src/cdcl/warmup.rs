use crate::{
    cdcl::decide::Deciding,
    solver::{Propagation, Solver},
};

impl Solver {
    fn propagate_beyond_conflicts(&mut self) {
        let saved = self.assignment.propagate;
        while self.assignment.propagate < self.assignment.trail.len() {
            let lit = self.assignment.trail[self.assignment.propagate];
            self.assignment.propagate += 1;
            let _ = self.propagate_literal(lit, Propagation::Beyond, None);
        }
        self.statistics.propagations +=
            u64::try_from(self.assignment.propagate - saved).unwrap_or(u64::MAX);
    }

    pub(crate) fn warmup(&mut self) {
        while self.assignment.unassigned > 0 && !self.terminated() {
            self.decide(Deciding::Warmup);
            self.propagate_beyond_conflicts();
        }
        self.backtrack_without_updating_phases(0);
    }
}
