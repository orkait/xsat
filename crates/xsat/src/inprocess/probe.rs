use crate::{
    cdcl::kimits::nlogpown,
    inprocess::substitute::Effort,
    options::Opt,
    solver::{Outcome, Solver},
    store::convert::{real, truncate},
};

impl Solver {
    pub(crate) fn init_probe_limit(&mut self) {
        let enabled = self.option(Opt::Simplify) != 0
            && self.option(Opt::Probe) != 0
            && (self.option(Opt::Substitute) != 0
                || self.option(Opt::Sweep) != 0
                || self.option(Opt::Vivify) != 0);
        self.limits.probe = enabled.then(|| {
            self.statistics.conflicts + self.scale_delta(u64::from(self.option_u32(Opt::Probeinit)))
        });
    }

    pub(crate) fn probing_due(&self) -> bool {
        let conflicts = self.statistics.conflicts;
        self.limits
            .probe
            .is_some_and(|limit| self.last.reduce != conflicts && limit < conflicts)
    }

    fn probe_round(&mut self) {
        self.backtrack_propagate_and_flush_trail();
        let _ = self.congruence();
        self.substitute(Effort::Bounded);
        self.binary_clauses_backbone();
        self.vivify();
        let _ = self.sweep();
        self.substitute(Effort::Bounded);
        self.transitive_reduction();
        self.binary_clauses_backbone();
        self.factor();
    }

    pub(crate) fn probe_initially(&mut self) {
        self.statistics.probings += 1;
        self.probing = true;
        let mut substitute_at_the_end = true;
        if self.option(Opt::Preprocesscongruence) != 0 && self.congruence() {
            self.substitute(Effort::Complete);
            substitute_at_the_end = false;
        }
        if self.option(Opt::Preprocessbackbone) != 0 {
            self.binary_clauses_backbone();
        }
        if self.option(Opt::Preprocessweep) != 0 && self.sweep() {
            self.substitute(Effort::Complete);
            substitute_at_the_end = false;
        }
        if substitute_at_the_end {
            self.substitute(Effort::Bounded);
        }
        if self.option(Opt::Preprocessfactor) != 0 {
            self.factor();
        }
        self.probing = false;
    }

    pub(crate) fn probe(&mut self) -> Option<Outcome> {
        self.statistics.probings += 1;
        self.probing = true;
        for _ in 0..self.option_u32(Opt::Proberounds) {
            let before = self.active_count;
            self.probe_round();
            if self.inconsistent || before == self.active_count {
                break;
            }
        }
        self.classify();
        if !self.inconsistent {
            let interval = real(u64::from(self.option_u32(Opt::Probeint)));
            let delta = truncate(interval * nlogpown(self.statistics.probings, 1));
            self.limits.probe = Some(self.statistics.conflicts + self.scale_delta(delta));
        }
        self.last.probe_ticks = self.statistics.search_ticks;
        self.probing = false;
        self.inconsistent.then_some(Outcome::Unsatisfiable)
    }
}
