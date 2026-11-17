use crate::{
    options::Opt,
    solver::{idx, not, Flush, Mode, Propagation, Solver, FALSE, TRUE, UNASSIGNED},
    store::{
        convert::widen,
        sort,
        watch::{self, Head, Removal},
    },
};

const ILLEGAL_LIT: u32 = (1 << 31) - 1;

impl Solver {
    fn transitive_assign(&mut self, lit: u32) {
        self.assignment.values[widen(lit)] = TRUE;
        self.assignment.values[widen(not(lit))] = FALSE;
        self.assignment.trail.push(lit);
    }

    fn transitive_backtrack(&mut self, saved: usize) {
        for &lit in &self.assignment.trail[saved..] {
            self.assignment.values[widen(lit)] = UNASSIGNED;
            self.assignment.values[widen(not(lit))] = UNASSIGNED;
        }
        self.assignment.trail.truncate(saved);
        self.assignment.propagate = saved;
        self.assignment.level = 0;
    }

    pub(crate) fn prioritize_binaries(&mut self) {
        let mut large = Vec::new();
        for watches in &mut self.clauses.watches {
            let (mut p, mut q) = (0, 0);
            while p < watches.len() {
                let head = watches[p];
                p += 1;
                if let Head::Binary(_) = watch::decode(head) {
                    watches[q] = head;
                    q += 1;
                } else {
                    large.extend([head, watches[p]]);
                    p += 1;
                }
            }
            watches.truncate(q);
            watches.append(&mut large);
        }
    }

    fn transitive_propagate(&mut self, src: u32, p: usize, dst: u32) -> (bool, bool) {
        let mut transitive = false;
        let mut failed = false;
        let mut ticks = 0;
        let mut propagate = self.assignment.propagate;
        while !transitive && !failed && propagate < self.assignment.trail.len() {
            let not_lit = not(self.assignment.trail[propagate]);
            propagate += 1;
            let watches = std::mem::take(&mut self.clauses.watches[widen(not_lit)]);
            ticks += 1 + watch::cache_lines(watches.len());
            for (q, &word) in watches.iter().enumerate() {
                if not_lit == src && q == p {
                    continue;
                }
                let Head::Binary(other) = watch::decode(word) else {
                    break;
                };
                if not_lit == src && other == ILLEGAL_LIT {
                    continue;
                }
                if other == dst {
                    transitive = true;
                    break;
                }
                let value = self.value(other);
                if value < 0 {
                    failed = true;
                    break;
                }
                if value == 0 {
                    self.transitive_assign(other);
                }
            }
            self.clauses.watches[widen(not_lit)] = watches;
        }
        let propagated = propagate - self.assignment.propagate;
        self.statistics.propagations += u64::try_from(propagated).unwrap_or(0);
        self.statistics.transitive_ticks += ticks;
        self.statistics.probing_ticks += ticks;
        (transitive, failed)
    }

    fn transitive_reduce(&mut self, src: u32, limit: u64) {
        let size = self.clauses.watches[widen(src)].len();
        let ticks = 1 + watch::cache_lines(size);
        self.statistics.transitive_ticks += ticks;
        self.statistics.probing_ticks += ticks;
        let mut reduced = false;
        let mut failed = false;
        for p in 0..size {
            let Head::Binary(dst) = watch::decode(self.clauses.watches[widen(src)][p]) else {
                break;
            };
            if dst < src || self.value(dst) != 0 {
                continue;
            }
            let saved = self.assignment.propagate;
            self.assignment.level = 1;
            self.transitive_assign(not(src));
            let (transitive, failing) = self.transitive_propagate(src, p, dst);
            failed = failing;
            self.transitive_backtrack(saved);
            if transitive {
                watch::remove_binary(&mut self.clauses.watches[widen(dst)], src, Removal::First);
                self.delete_binary(src, dst);
                self.clauses.watches[widen(src)][p] = watch::binary(ILLEGAL_LIT);
                reduced = true;
            }
            if failed || self.statistics.transitive_ticks > limit || self.terminated() {
                break;
            }
        }
        if reduced {
            watch::remove_binary(
                &mut self.clauses.watches[widen(src)],
                ILLEGAL_LIT,
                Removal::All,
            );
        }
        if failed {
            self.learned_unit(src);
            let _ = self.propagate_trail(Propagation::Probing, None, Flush::Trail);
        }
    }

    pub(crate) fn transitive_reduction(&mut self) {
        if self.inconsistent || self.option(Opt::Transitive) == 0 || self.terminated() {
            return;
        }
        self.prioritize_binaries();
        let limit = self.effort_limit(Opt::Transitiveeffort, self.statistics.transitive_ticks);
        let mut probes: Vec<u32> = (0..self.vars)
            .filter(|&idx| self.active[widen(idx)])
            .collect();
        match self.mode {
            Mode::Stable => sort::sort(&mut probes, |a, b| {
                let (i, j) = (idx(a), idx(b));
                let (s, t) = (self.scores.score(i), self.scores.score(j));
                s < t || s <= t && i < j
            }),
            Mode::Focused => sort::sort(&mut probes, |a, b| {
                self.queue.links[widen(idx(a))].stamp < self.queue.links[widen(idx(b))].stamp
            }),
        }
        'probing: while let Some(idx) = probes.pop() {
            if !self.active[widen(idx)] {
                continue;
            }
            for lit in [2 * idx, 2 * idx + 1] {
                if self.value(lit) != 0 {
                    continue;
                }
                self.transitive_reduce(lit, limit);
                if self.inconsistent
                    || self.statistics.transitive_ticks > limit
                    || self.terminated()
                {
                    break 'probing;
                }
            }
        }
    }
}
