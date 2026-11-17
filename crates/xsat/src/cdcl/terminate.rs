use std::sync::{
    atomic::{AtomicBool, Ordering},
    Arc,
};

use crate::solver::Solver;

#[derive(Clone, Debug, Default)]
pub struct Terminator(Arc<AtomicBool>);

impl Terminator {
    pub fn terminate(&self) {
        self.0.store(true, Ordering::Relaxed);
    }

    pub(crate) fn terminated(&self) -> bool {
        self.0.load(Ordering::Relaxed)
    }

    fn reset(&self) {
        self.0.store(false, Ordering::Relaxed);
    }
}

impl Solver {
    #[must_use]
    pub fn terminator(&self) -> Terminator {
        Terminator::clone(&self.terminator)
    }

    pub(crate) fn terminated(&self) -> bool {
        self.terminator.terminated()
    }

    pub(crate) fn reset_termination(&self) {
        self.terminator.reset();
    }
}
