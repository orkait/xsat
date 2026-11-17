use crate::{
    cdcl::kimits::nlogpown,
    options::Opt,
    solver::{Mode, Solver},
    store::convert::{real, truncate, widen},
};

const REPHASE_EXPONENT: u32 = 3;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Rephase {
    Best,
    Walking,
    Inverted,
    Original,
}

const SCHEDULE: [Rephase; 6] = [
    Rephase::Best,
    Rephase::Walking,
    Rephase::Inverted,
    Rephase::Best,
    Rephase::Walking,
    Rephase::Original,
];

impl Solver {
    pub(crate) fn rephasing(&self) -> bool {
        self.option(Opt::Rephase) != 0
            && self.mode == Mode::Stable
            && self.statistics.conflicts > self.limits.rephase
    }

    pub(crate) fn rephase(&mut self) {
        self.backtrack_propagate_and_flush_trail();
        self.statistics.rephased += 1;
        let count = self.statistics.rephased;
        let rephase = SCHEDULE[widen(u32::try_from((count - 1) % 6).unwrap_or(0))];
        let initial = self.initial_phase();
        match rephase {
            Rephase::Best => {
                for (saved, &best) in self.phases.saved.iter_mut().zip(&self.phases.best) {
                    if best != 0 {
                        *saved = best;
                    }
                }
            }
            Rephase::Walking => self.walk(),
            Rephase::Inverted => self.phases.saved.fill(-initial),
            Rephase::Original => self.phases.saved.fill(initial),
        }
        self.phases.target.copy_from_slice(&self.phases.saved);
        if !self.inconsistent {
            let interval = real(u64::from(self.option_u32(Opt::Rephaseint)));
            let delta = truncate(interval * nlogpown(count, REPHASE_EXPONENT));
            self.limits.rephase = self.statistics.conflicts + delta;
        }
        self.phases.target_assigned = 0;
        if rephase == Rephase::Best {
            self.phases.best_assigned = 0;
        }
    }
}
