use crate::{solver::UNASSIGNED, store::convert::widen};

#[derive(Debug, Default)]
pub(crate) struct Phases {
    pub(crate) saved: Vec<i8>,
    pub(crate) target: Vec<i8>,
    pub(crate) best: Vec<i8>,
    pub(crate) target_assigned: u32,
    pub(crate) best_assigned: u32,
}

impl Phases {
    pub(crate) fn resize(&mut self, vars: u32) {
        for phases in [&mut self.saved, &mut self.target, &mut self.best] {
            phases.resize(widen(vars), UNASSIGNED);
        }
    }

    pub(crate) fn update(&mut self, assigned: u32, values: &[i8]) {
        if self.target_assigned < assigned {
            self.target_assigned = assigned;
            save(&mut self.target, values);
        }
        if self.best_assigned < assigned {
            self.best_assigned = assigned;
            save(&mut self.best, values);
        }
    }

    pub(crate) fn recount(&mut self, active: &[bool]) {
        let assigned = |phases: &[i8]| {
            let count = phases
                .iter()
                .zip(active)
                .filter(|&(&phase, &active)| active && phase != 0)
                .count();
            u32::try_from(count).unwrap_or(u32::MAX)
        };
        self.target_assigned = assigned(&self.target);
        self.best_assigned = assigned(&self.best);
    }

    pub(crate) fn compact(&mut self, dst: usize, src: usize) {
        for phases in [&mut self.saved, &mut self.target, &mut self.best] {
            phases[dst] = phases[src];
        }
    }
}

fn save(phases: &mut [i8], values: &[i8]) {
    for (phase, &value) in phases.iter_mut().zip(values.iter().step_by(2)) {
        if value != UNASSIGNED {
            *phase = value;
        }
    }
}
