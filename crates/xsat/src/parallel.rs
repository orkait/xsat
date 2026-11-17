use std::collections::HashSet;

use crate::{
    error::SolverError,
    options::{Opt, Options},
    solver::{Outcome, Solver},
    store::convert::widen,
};

const FIRST_EPOCH: u64 = 1_000;
const LAST_EPOCH: u64 = 64_000;
const PHASES: i32 = 2;
const MODES: usize = 3;
const STABLE_ONLY: i32 = 2;

#[derive(Debug)]
pub struct Portfolio {
    workers: Vec<Solver>,
    shared: HashSet<i32>,
    winner: usize,
}

impl Portfolio {
    #[must_use]
    pub fn new(options: &Options, workers: usize) -> Portfolio {
        let workers = (0..workers.max(1))
            .map(|worker| Solver::new(diversified(options, worker)))
            .collect();
        Portfolio {
            workers,
            shared: HashSet::new(),
            winner: 0,
        }
    }

    pub fn reserve(&mut self, variables: u32) -> Result<(), SolverError> {
        for worker in &mut self.workers {
            worker.reserve(variables)?;
        }
        Ok(())
    }

    pub fn add(&mut self, elit: i32) -> Result<(), SolverError> {
        for worker in &mut self.workers {
            worker.add(elit)?;
        }
        Ok(())
    }

    pub fn solve(&mut self) -> Result<Outcome, SolverError> {
        for worker in &self.workers {
            worker.input_closed()?;
        }
        let mut epoch = FIRST_EPOCH;
        loop {
            let outcomes: Vec<Result<Outcome, SolverError>> = std::thread::scope(|scope| {
                let running: Vec<_> = self
                    .workers
                    .iter_mut()
                    .map(|worker| {
                        scope.spawn(move || {
                            worker.limit_conflicts(epoch);
                            worker.solve()
                        })
                    })
                    .collect();
                running
                    .into_iter()
                    .map(|thread| match thread.join() {
                        Ok(outcome) => outcome,
                        Err(panic) => std::panic::resume_unwind(panic),
                    })
                    .collect()
            });
            let outcomes = outcomes.into_iter().collect::<Result<Vec<_>, _>>()?;
            if let Some(winner) = outcomes
                .iter()
                .position(|&outcome| outcome != Outcome::Unknown)
            {
                self.winner = winner;
                return Ok(outcomes[winner]);
            }
            self.share_units();
            epoch = (epoch * 2).min(LAST_EPOCH);
        }
    }

    fn share_units(&mut self) {
        let fresh: Vec<i32> = self
            .workers
            .iter()
            .flat_map(|worker| {
                worker.units.iter().copied().filter(|unit| {
                    !worker
                        .extension
                        .get(widen(unit.unsigned_abs()))
                        .copied()
                        .unwrap_or(false)
                })
            })
            .filter(|&unit| self.shared.insert(unit))
            .collect();
        for worker in &mut self.workers {
            for &unit in &fresh {
                if worker.eliminated_slot(unit).is_none() {
                    worker.add_external(unit);
                    worker.add_external(0);
                }
            }
        }
    }

    #[must_use]
    pub fn winner(&self) -> &Solver {
        &self.workers[self.winner]
    }
}

fn diversified(options: &Options, worker: usize) -> Options {
    let mut options = options.clone();
    if worker > 0 {
        let seed = i32::try_from(worker).unwrap_or(i32::MAX);
        let _ = options.set(Opt::Seed, seed);
        let _ = options.set(Opt::Phase, (options.get(Opt::Phase) + seed) % PHASES);
        let _ = options.set(
            Opt::Stable,
            i32::try_from(worker % MODES).unwrap_or(STABLE_ONLY),
        );
    }
    options
}
