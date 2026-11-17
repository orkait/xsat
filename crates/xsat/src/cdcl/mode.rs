use crate::{
    cdcl::kimits::nlogpown,
    options::Opt,
    solver::{Mode, Solver},
    store::convert::{real, truncate},
};

const SWITCHING: i32 = 1;
const MODE_EXPONENT: u32 = 4;

impl Solver {
    pub(crate) fn init_mode_limit(&mut self) {
        if self.option(Opt::Stable) != SWITCHING {
            return;
        }
        self.limits.mode_conflicts =
            self.statistics.conflicts + u64::from(self.option_u32(Opt::Modeinit));
        self.limits.mode_ticks = 0;
        self.limits.mode_count = 0;
        self.mode_ticks = self.statistics.search_ticks;
    }

    pub(crate) fn switching_search_mode(&self) -> bool {
        if self.option(Opt::Stable) != SWITCHING {
            return false;
        }
        if self.limits.mode_count % 2 == 1 {
            self.statistics.search_ticks >= self.limits.mode_ticks
        } else {
            self.statistics.conflicts >= self.limits.mode_conflicts
        }
    }

    fn update_mode_limit(&mut self, delta_ticks: u64) {
        self.init_averages();
        if self.limits.mode_count % 2 == 1 {
            self.limits.mode_ticks = self.statistics.search_ticks + delta_ticks;
        } else {
            let interval = real(u64::from(self.option_u32(Opt::Modeint)));
            let count = self.statistics.switched.div_ceil(2);
            let scaled = truncate(interval * nlogpown(count, MODE_EXPONENT));
            self.limits.mode_conflicts = self.statistics.conflicts + scaled;
        }
        self.mode_ticks = self.statistics.search_ticks;
    }

    pub(crate) fn switch_search_mode(&mut self) {
        self.statistics.switched += 1;
        self.limits.mode_count += 1;
        let delta_ticks = self.statistics.search_ticks - self.mode_ticks;
        match self.mode {
            Mode::Stable => {
                self.mode = Mode::Focused;
                self.update_mode_limit(delta_ticks);
                self.queue.reset_search();
                self.update_focused_restart_limit();
            }
            Mode::Focused => {
                self.mode = Mode::Stable;
                self.update_mode_limit(delta_ticks);
                self.init_reluctant();
                self.update_scores();
            }
        }
        self.averages[self.mode.index()].saved_decisions = self.statistics.decisions;
        self.start_random_sequence();
    }
}
