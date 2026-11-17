use crate::{
    options::Opt,
    solver::{idx, literal, not, Mode, Solver},
    store::{
        convert::{real, truncate, widen},
        watch,
    },
};

const REORDER_FOCUSED: i32 = 2;
const SMALLEST_SIZE: u32 = 2;

impl Solver {
    pub(crate) fn reordering(&self) -> bool {
        let reorder = self.option(Opt::Reorder);
        reorder != 0
            && (self.mode == Mode::Stable || reorder >= REORDER_FOCUSED)
            && self.assignment.level == 0
            && self.statistics.conflicts >= self.limits.reorder
    }

    fn compute_weights(&self) -> Vec<f64> {
        let mut weights = vec![0.0_f64; 2 * widen(self.vars)];
        let max_size = self.option_u32(Opt::Reordermaxsize);
        let mut table = vec![0.0; widen(max_size) + 1];
        let mut weight = 1.0;
        for size in SMALLEST_SIZE..=max_size {
            table[widen(size)] = weight;
            weight /= 2.0;
        }
        for at in self.clauses.arena.refs() {
            if self.clauses.last_irredundant.is_some_and(|last| last < at) {
                break;
            }
            if self.clauses.arena.redundant(at) || self.clauses.arena.garbage(at) {
                continue;
            }
            let lits = self.clauses.arena.lits(at);
            let mut size = 0;
            let mut satisfied = false;
            for &lit in lits {
                let value = self.value(lit);
                if value > 0 {
                    satisfied = true;
                    break;
                }
                if value == 0 && size < max_size {
                    size += 1;
                    if size == max_size {
                        break;
                    }
                }
            }
            if satisfied {
                continue;
            }
            for &lit in lits {
                weights[widen(lit)] += table[widen(size)];
            }
        }
        let binary_weight = table[widen(SMALLEST_SIZE)];
        for lit in 0..2 * self.vars {
            if !self.active[widen(idx(lit))] {
                continue;
            }
            for other in watch::binaries(&self.clauses.watches[widen(lit)]) {
                if other < lit || !self.active[widen(idx(other))] {
                    continue;
                }
                weights[widen(lit)] += binary_weight;
                weights[widen(other)] += binary_weight;
            }
        }
        (0..self.vars)
            .map(|var| {
                let (pos, neg) = (
                    weights[widen(literal(var))],
                    weights[widen(not(literal(var)))],
                );
                pos.max(neg) + 2.0 * pos.min(neg)
            })
            .collect()
    }

    fn sort_active_variables_by_weight(&self, weights: &[f64]) -> Vec<u32> {
        let mut sorted: Vec<u32> = (0..self.vars)
            .filter(|&var| self.active[widen(var)])
            .collect();
        sorted.sort_by(|&a, &b| {
            let by_weight = weights[widen(a)].total_cmp(&weights[widen(b)]);
            match self.mode {
                Mode::Stable => by_weight
                    .then(self.scores.score(a).total_cmp(&self.scores.score(b)))
                    .then(b.cmp(&a)),
                Mode::Focused => by_weight.then(
                    self.queue.links[widen(a)]
                        .stamp
                        .cmp(&self.queue.links[widen(b)].stamp),
                ),
            }
        });
        sorted
    }

    pub(crate) fn reorder(&mut self) {
        self.statistics.reordered += 1;
        let weights = self.compute_weights();
        match self.mode {
            Mode::Focused => {
                for idx in self.sort_active_variables_by_weight(&weights) {
                    self.move_to_front(idx);
                }
            }
            Mode::Stable => {
                self.rescale_scores();
                for idx in self
                    .sort_active_variables_by_weight(&weights)
                    .into_iter()
                    .rev()
                {
                    let score = self.scores.score(idx) + weights[widen(idx)];
                    self.scores.update(idx, score);
                }
            }
        }
        let interval = real(u64::from(self.option_u32(Opt::Reorderint)));
        let delta = truncate(interval * real(self.statistics.reordered));
        self.limits.reorder = self.statistics.conflicts + delta;
    }
}
