use crate::{
    cdcl::kimits::logn,
    options::Opt,
    solver::{literal, not, Mode, Solver},
    store::convert::{truncate, widen},
};

const POSITIVE: i8 = 1;
const NEGATIVE: i8 = -1;
const SWITCH_PHASES: u64 = 7;
const SWITCH_INITIAL: u64 = 1;
const SWITCH_INVERTED: u64 = 3;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Deciding {
    Search,
    Warmup,
}

impl Solver {
    pub(crate) fn initial_phase(&self) -> i8 {
        if self.option(Opt::Phase) == 0 {
            NEGATIVE
        } else {
            POSITIVE
        }
    }

    fn last_enqueued_unassigned_variable(&mut self) -> u32 {
        let mut res = self.queue.search_idx;
        if self.value(literal(res)) != 0 {
            while self.value(literal(res)) != 0 {
                res = self.queue.prev(res);
            }
            self.queue.update(res);
        }
        res
    }

    fn largest_score_unassigned_variable(&mut self) -> u32 {
        let mut res = self.scores.max();
        while self.value(literal(res)) != 0 {
            let _ = self.scores.pop_max();
            res = self.scores.max();
        }
        res
    }

    fn random_decisions(&self) -> bool {
        self.option(Opt::Randec) != 0
            && match self.mode {
                Mode::Stable => self.option(Opt::Randecstable) != 0,
                Mode::Focused => self.option(Opt::Randecfocused) != 0,
            }
    }

    pub(crate) fn start_random_sequence(&mut self) {
        if !self.random_decisions() || self.randec > 0 {
            return;
        }
        self.statistics.random_sequences += 1;
        let scale = logn(self.statistics.random_sequences);
        let length = truncate(f64::from(self.option(Opt::Randeclength)) * scale);
        self.randec = u32::try_from(length).unwrap_or(u32::MAX);
        if !self.inconsistent {
            let delta = truncate(f64::from(self.option(Opt::Randecint)) * scale);
            self.limits.randec = self.statistics.conflicts + delta;
        }
    }

    fn next_random_decision(&mut self, deciding: Deciding) -> Option<u32> {
        if self.vars == 0 || deciding == Deciding::Warmup || !self.random_decisions() {
            return None;
        }
        if self.randec == 0 {
            if self.assignment.level > 1 || self.statistics.conflicts < self.limits.randec {
                return None;
            }
            self.start_random_sequence();
        }
        loop {
            let idx = self.random.next32() % self.vars;
            if self.active[widen(idx)] && self.value(literal(idx)) == 0 {
                return Some(idx);
            }
        }
    }

    pub(crate) fn next_decision_variable(&mut self, deciding: Deciding) -> u32 {
        if let Some(idx) = self.next_random_decision(deciding) {
            return idx;
        }
        match self.mode {
            Mode::Stable => self.largest_score_unassigned_variable(),
            Mode::Focused => self.last_enqueued_unassigned_variable(),
        }
    }

    pub(crate) fn decide_phase(&self, idx: u32) -> i8 {
        let force = self.option(Opt::Forcephase) != 0;
        let target = self.option(Opt::Target);
        let use_target = !force && target != 0 && (self.mode == Mode::Stable || target > 1);
        let use_saved = !force && self.option(Opt::Phasesaving) != 0;
        let mut res = 0;
        if self.mode == Mode::Focused {
            match (self.statistics.switched >> 1) & SWITCH_PHASES {
                SWITCH_INITIAL => res = self.initial_phase(),
                SWITCH_INVERTED => res = -self.initial_phase(),
                _ => {}
            }
        }
        if res == 0 && use_target {
            res = self.phases.target[widen(idx)];
        }
        if res == 0 && use_saved {
            res = self.phases.saved[widen(idx)];
        }
        if res == 0 {
            res = self.initial_phase();
        }
        if res < 0 {
            NEGATIVE
        } else {
            POSITIVE
        }
    }

    pub(crate) fn decide(&mut self, deciding: Deciding) {
        if deciding == Deciding::Search {
            self.statistics.decisions += 1;
        }
        self.assignment.level += 1;
        let idx = self.next_decision_variable(deciding);
        let lit = if self.decide_phase(idx) < 0 {
            not(literal(idx))
        } else {
            literal(idx)
        };
        self.push_frame(lit);
        self.assign_decision(lit);
    }
}
