use crate::{
    options::Opt,
    solver::{idx, literal, negated, not, Reason, Solver},
    store::convert::{truncate, widen, PERCENT},
};

impl Solver {
    pub(crate) fn compacting(&self) -> bool {
        if self.option(Opt::Compact) == 0 {
            return false;
        }
        let inactive = self.vars - self.active_count;
        let limit = f64::from(self.option(Opt::Compactlim)) / PERCENT * f64::from(self.vars);
        u64::from(inactive) > truncate(limit)
    }

    fn fixed_variable(&self, idx: u32) -> bool {
        !self.active[widen(idx)] && self.value(literal(idx)) != 0
    }

    pub(crate) fn map_literal(&self, lit: u32) -> Option<u32> {
        let eidx = self.exports[widen(idx(lit))];
        if eidx == 0 {
            return None;
        }
        let mlit = self.imports[widen(eidx)]?;
        Some(if negated(lit) { not(mlit) } else { mlit })
    }

    fn map_idx(&self, iidx: u32) -> Option<u32> {
        self.map_literal(literal(iidx)).map(idx)
    }

    pub(crate) fn compact_literals(&mut self) -> (u32, Option<u32>) {
        let mut mfixed = None;
        let mut vars = 0;
        for iidx in 0..self.vars {
            let ilit = literal(iidx);
            let mlit = if self.fixed_variable(iidx) {
                let value = self.value(ilit);
                if let Some(fixed) = mfixed {
                    if value < 0 {
                        not(fixed)
                    } else {
                        fixed
                    }
                } else {
                    let mlit = literal(vars);
                    mfixed = Some(if value < 0 { not(mlit) } else { mlit });
                    vars += 1;
                    mlit
                }
            } else if self.active[widen(iidx)] {
                vars += 1;
                literal(vars - 1)
            } else {
                let eidx = self.exports[widen(iidx)];
                if eidx != 0 {
                    self.imports[widen(eidx)] = None;
                    self.exports[widen(iidx)] = 0;
                }
                continue;
            };
            if mlit != ilit {
                self.imports[widen(self.exports[widen(iidx)])] = Some(mlit);
            }
        }
        (vars, mfixed)
    }

    pub(crate) fn finalize_compacting(&mut self, vars: u32, mfixed: Option<u32>) {
        if vars == self.vars {
            return;
        }
        let mut first = true;
        for iidx in 0..self.vars {
            if first && self.fixed_variable(iidx) {
                first = false;
            } else if !self.active[widen(iidx)] {
                self.exports[widen(iidx)] = 0;
            }
        }
        let map: Vec<Option<u32>> = (0..self.vars).map(|iidx| self.map_idx(iidx)).collect();
        let map_literal = |lit: u32| {
            map[widen(idx(lit))].map(|midx| {
                if negated(lit) {
                    not(literal(midx))
                } else {
                    literal(midx)
                }
            })
        };
        for position in 0..self.assignment.trail.len() {
            let ilit = self.assignment.trail[position];
            self.assignment.trail[position] = map_literal(ilit).unwrap_or(ilit);
            let assigned = &mut self.assignment.assigned[widen(idx(ilit))];
            if let Reason::Binary(other) = assigned.reason() {
                assigned.set_reason(Reason::Binary(map_literal(other).unwrap_or(other)));
            }
        }
        for iidx in 0..self.vars {
            let ilit = literal(iidx);
            if let Some(mlit) = map_literal(ilit).filter(|&mlit| mlit != ilit) {
                self.compact_literal(mlit, ilit);
            }
        }
        if let Some(mfixed) = mfixed {
            for &elit in &self.units {
                let mlit = if elit < 0 { not(mfixed) } else { mfixed };
                self.imports[widen(elit.unsigned_abs())] = Some(mlit);
            }
        }
        self.queue.compact(&map);
        let schedule = std::mem::take(&mut self.sweeping.schedule);
        self.sweeping.schedule = schedule
            .into_iter()
            .filter_map(|idx| map[widen(idx)])
            .collect();
        self.scores = self.scores.compacted(vars, &map);
        for frame in &mut self.assignment.frames[1..] {
            frame.decision = frame.decision.and_then(map_literal);
        }
        for (iidx, &midx) in map.iter().enumerate() {
            let eidx = self.exports[iidx];
            if let (true, Some(midx)) = (eidx != 0, midx) {
                self.exports[widen(midx)] = eidx;
            }
        }
        self.decrease_size(vars);
        self.phases.recount(&self.active);
    }

    fn compact_literal(&mut self, dst: u32, src: u32) {
        let (dst_idx, src_idx) = (widen(idx(dst)), widen(idx(src)));
        self.assignment.assigned[dst_idx] = self.assignment.assigned[src_idx];
        self.active[dst_idx] = self.active[src_idx];
        self.flags[dst_idx] = self.flags[src_idx];
        self.phases.compact(dst_idx, src_idx);
        self.assignment.values[widen(dst)] = self.assignment.values[widen(src)];
        self.assignment.values[widen(not(dst))] = self.assignment.values[widen(not(src))];
    }
}
