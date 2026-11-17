use crate::{
    options::Opt,
    solver::Solver,
    store::convert::{real, truncate},
};

const LOG_OFFSET: u64 = 9;
const SCALE_OFFSET: f64 = 5.0;
const SCALE_SQUARE: f64 = 4.5;
const SCALE_BASE: f64 = 25.0;
const MILLION: f64 = 1e6;
const PER_MILLE_FRACTION: f64 = 1e-3;

#[derive(Clone, Copy, Debug, Default)]
pub(crate) struct Limits {
    pub(crate) conflicts: Option<u64>,
    pub(crate) decisions: Option<u64>,
    pub(crate) reduce: u64,
    pub(crate) probe: Option<u64>,
    pub(crate) glue_conflicts: u64,
    pub(crate) glue_interval: u64,
    pub(crate) mode_count: u64,
    pub(crate) mode_ticks: u64,
    pub(crate) mode_conflicts: u64,
    pub(crate) randec: u64,
    pub(crate) reorder: u64,
    pub(crate) rephase: u64,
    pub(crate) restart: u64,
}

#[derive(Clone, Copy, Debug, Default)]
pub(crate) struct Last {
    pub(crate) reduce: u64,
    pub(crate) probe_ticks: u64,
}

pub(crate) fn logn(count: u64) -> f64 {
    real(count + LOG_OFFSET).log10()
}

pub(crate) fn nlogpown(count: u64, exponent: u32) -> f64 {
    let log = logn(count);
    let mut factor = 1.0;
    for _ in 0..exponent {
        factor *= log;
    }
    real(count) * factor
}

#[derive(Clone, Copy, Debug, Default)]
pub(crate) struct Delay {
    count: u32,
    current: u32,
}

impl Delay {
    pub(crate) fn reduce(&mut self) {
        if self.current == 0 {
            return;
        }
        self.current /= 2;
        self.count = self.current;
    }

    pub(crate) fn bump(&mut self) {
        self.current = self.current.saturating_add(1);
        self.count = self.current;
    }

    pub(crate) fn delaying(&mut self) -> bool {
        if self.count == 0 {
            return false;
        }
        self.count -= 1;
        true
    }
}

impl Solver {
    pub(crate) fn scale_delta(&self, delta: u64) -> u64 {
        let clauses = self.statistics.clauses_binary + self.statistics.clauses_irredundant;
        let f = logn(clauses + 1) - SCALE_OFFSET;
        let fff = SCALE_SQUARE * (f * f) + SCALE_BASE;
        truncate(fff * real(delta))
    }

    pub(crate) fn effort_limit(&self, effort: Opt, start: u64) -> u64 {
        let minimum = truncate(MILLION * f64::from(self.option(Opt::Mineffort)));
        let last = if self.probing {
            self.last.probe_ticks
        } else {
            self.elimination.last_ticks
        };
        let reference = (self.statistics.search_ticks - last).max(minimum);
        let fraction = f64::from(self.option(effort)) * PER_MILLE_FRACTION;
        start + truncate(fraction * real(reference))
    }
}
