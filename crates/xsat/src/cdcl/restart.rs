use crate::{
    cdcl::{decide::Deciding, kimits::logn},
    options::Opt,
    solver::{idx, Mode, Solver},
    store::convert::{real, truncate, widen, PERCENT},
};

impl Solver {
    pub(crate) fn restarting(&mut self) -> bool {
        if self.option(Opt::Restart) == 0
            || self.assignment.level == 0
            || self.statistics.conflicts < self.limits.restart
        {
            return false;
        }
        match self.mode {
            Mode::Stable => self.reluctant.triggered(),
            Mode::Focused => {
                let averages = &self.averages[self.mode.index()];
                let margin = (PERCENT + f64::from(self.option(Opt::Restartmargin))) / PERCENT;
                margin * averages.slow_glue.value <= averages.fast_glue.value
            }
        }
    }

    pub(crate) fn update_focused_restart_limit(&mut self) {
        let restarts = self.statistics.restarts;
        let mut delta = u64::from(self.option_u32(Opt::Restartint));
        if restarts > 0 {
            delta = truncate(real(delta) + (logn(restarts) - 1.0));
        }
        self.limits.restart = self.statistics.conflicts + delta;
    }

    fn reuse_trail(&mut self) -> u32 {
        if self.option(Opt::Restartreusetrail) == 0 {
            return 0;
        }
        let next = self.next_decision_variable(Deciding::Search);
        let mut reused = 0;
        while reused < self.assignment.level {
            let Some(decision) = self.assignment.frames[widen(reused + 1)].decision else {
                break;
            };
            let above = match self.mode {
                Mode::Stable => self.scores.score(idx(decision)) > self.scores.score(next),
                Mode::Focused => {
                    let links = &self.queue.links;
                    links[widen(idx(decision))].stamp > links[widen(next)].stamp
                }
            };
            if !above {
                break;
            }
            reused += 1;
        }
        reused
    }

    pub(crate) fn restart(&mut self) {
        self.statistics.restarts += 1;
        let level = self.reuse_trail();
        self.backtrack_in_consistent_state(level);
        if self.mode == Mode::Focused {
            self.update_focused_restart_limit();
        }
    }
}
