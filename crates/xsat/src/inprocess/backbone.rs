use crate::{
    options::Opt,
    solver::{idx, not, Flush, Propagation, Reason, Solver, FALSE, TRUE, UNASSIGNED},
    store::{
        convert::widen,
        flags::Flag,
        watch::{self, Head},
    },
};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Watching {
    Sparse,
    Dense,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Order {
    Mixed,
    BinariesFirst,
}

fn backbone_flag(lit: u32) -> Flag {
    Flag::of(lit, Flag::Backbone0, Flag::Backbone1)
}

impl Solver {
    fn schedule_backbone_candidates(&self) -> Vec<u32> {
        let mut candidates = Vec::new();
        let mut not_rescheduled = false;
        let active = (0..self.vars).filter(|&idx| self.active[widen(idx)]);
        for idx in active.clone() {
            for lit in [2 * idx, 2 * idx + 1] {
                if self.flags[widen(idx)].has(backbone_flag(lit)) {
                    candidates.push(lit);
                } else {
                    not_rescheduled = true;
                }
            }
        }
        if not_rescheduled {
            for idx in active {
                for lit in [2 * idx, 2 * idx + 1] {
                    if !self.flags[widen(idx)].has(backbone_flag(lit)) {
                        candidates.push(lit);
                    }
                }
            }
        }
        candidates
    }

    fn keep_backbone_candidates(&mut self, candidates: &[u32]) {
        let remaining = candidates
            .iter()
            .filter(|&&lit| self.active[widen(idx(lit))]);
        let mut remain = 0;
        let mut prioritized = 0;
        for &lit in remaining.clone() {
            remain += 1;
            if self.flags[widen(idx(lit))].has(backbone_flag(lit)) {
                prioritized += 1;
            }
        }
        if remain == 0 || prioritized != 0 {
            return;
        }
        let remaining: Vec<u32> = remaining.copied().collect();
        for lit in remaining {
            self.flags[widen(idx(lit))].set(backbone_flag(lit));
        }
    }

    fn backbone_assign(&mut self, lit: u32, reason: Reason) {
        self.assignment.values[widen(lit)] = TRUE;
        self.assignment.values[widen(not(lit))] = FALSE;
        self.assignment.trail.push(lit);
        let assigned = &mut self.assignment.assigned[widen(idx(lit))];
        assigned.set_reason(reason);
        assigned.level = self.assignment.level;
    }

    fn backbone_propagate_literal(&mut self, lit: u32, ticks: &mut u64) -> Option<[u32; 2]> {
        let not_lit = not(lit);
        let stop_early = self.clauses.order == Order::BinariesFirst;
        let watches = std::mem::take(&mut self.clauses.watches[widen(not_lit)]);
        let mut p = 0;
        let mut conflict = None;
        while p < watches.len() {
            let head = watches[p];
            p += 1;
            match watch::decode(head) {
                Head::Binary(other) => {
                    let value = self.value(other);
                    if value > 0 {
                        continue;
                    }
                    if value < 0 {
                        conflict = Some([not_lit, other]);
                        break;
                    }
                    self.backbone_assign(other, Reason::Binary(lit));
                }
                Head::Blocking(_) => {
                    if stop_early {
                        break;
                    }
                    p += 1;
                }
            }
        }
        if conflict.is_none() {
            *ticks += 1 + watch::cache_lines(p);
        }
        self.clauses.watches[widen(not_lit)] = watches;
        conflict
    }

    fn backbone_propagate(&mut self) -> Option<[u32; 2]> {
        let mut ticks = 0;
        let saved = self.assignment.propagate;
        let mut conflict = None;
        while conflict.is_none() && self.assignment.propagate < self.assignment.trail.len() {
            let lit = self.assignment.trail[self.assignment.propagate];
            self.assignment.propagate += 1;
            conflict = self.backbone_propagate_literal(lit, &mut ticks);
        }
        self.statistics.propagations +=
            u64::try_from(self.assignment.propagate - saved).unwrap_or(0);
        self.statistics.backbone_ticks += ticks;
        self.statistics.probing_ticks += ticks;
        conflict
    }

    fn backbone_backtrack(&mut self, saved: usize, level: u32) {
        for &lit in &self.assignment.trail[saved..] {
            self.assignment.values[widen(lit)] = UNASSIGNED;
            self.assignment.values[widen(not(lit))] = UNASSIGNED;
        }
        self.assignment.trail.truncate(saved);
        self.assignment.level = level;
        self.assignment.propagate = saved;
    }

    fn backbone_analyze(&mut self, conflict: [u32; 2]) -> u32 {
        self.push_analyzed(idx(conflict[0]));
        self.push_analyzed(idx(conflict[1]));
        let mut t = self.assignment.trail.len();
        let dominator = loop {
            t -= 1;
            let lit = self.assignment.trail[t];
            let assigned = self.assignment.assigned[widen(idx(lit))];
            if !assigned.analyzed {
                continue;
            }
            let Reason::Binary(reason) = assigned.reason() else {
                break lit;
            };
            if self.assignment.assigned[widen(idx(reason))].analyzed {
                break reason;
            }
            self.push_analyzed(idx(reason));
        };
        self.clear_analyzed();
        dominator
    }

    fn drop_backbone_candidates(&mut self, candidates: &mut Vec<u32>) {
        let mut q = 0;
        for p in 0..candidates.len() {
            let probe = candidates[p];
            candidates[q] = probe;
            q += 1;
            if self.value(probe) > 0 {
                q -= 1;
                self.flags[widen(idx(probe))].clear(backbone_flag(probe));
            }
        }
        candidates.truncate(q);
    }

    fn compute_backbone(&mut self) {
        let mut failed = 0;
        let mut units = Vec::new();
        let mut candidates = self.schedule_backbone_candidates();
        let ticks_limit = self.effort_limit(Opt::Backboneeffort, self.statistics.backbone_ticks);
        let round_limit = (u64::from(self.option_u32(Opt::Backbonerounds))
            * self.statistics.backbone_computations)
            .min(u64::from(self.option_u32(Opt::Backbonemaxrounds)));
        let mut round = 0;
        let mut inconsistent = None;
        loop {
            if round >= round_limit
                || self.statistics.backbone_ticks > ticks_limit
                || self.terminated()
            {
                break;
            }
            let previous = failed;
            round += 1;
            let mut q = 0;
            let mut p = 0;
            while p < candidates.len() {
                let probe = candidates[p];
                candidates[q] = probe;
                p += 1;
                q += 1;
                let value = self.value(probe);
                if value > 0 {
                    q -= 1;
                    self.flags[widen(idx(probe))].clear(backbone_flag(probe));
                    continue;
                }
                if value < 0 {
                    if self.level_of(probe) == 0 {
                        q -= 1;
                    }
                    continue;
                }
                if self.statistics.backbone_ticks > ticks_limit || self.terminated() {
                    break;
                }
                let level = self.assignment.level;
                let saved = self.assignment.trail.len();
                self.assignment.level = level + 1;
                self.backbone_assign(probe, Reason::Decision);
                let Some(conflict) = self.backbone_propagate() else {
                    continue;
                };
                failed += 1;
                q -= 1;
                let not_uip = not(self.backbone_analyze(conflict));
                self.backbone_backtrack(saved, level);
                units.push(not_uip);
                self.backbone_assign(not_uip, Reason::Unit);
                if self.backbone_propagate().is_some() {
                    inconsistent = Some(not_uip);
                    break;
                }
            }
            candidates.copy_within(p.., q);
            candidates.truncate(q + candidates.len() - p);
            if inconsistent.is_none() {
                self.drop_backbone_candidates(&mut candidates);
            }
            if !self.assignment.trail.is_empty() {
                self.backbone_backtrack(0, 0);
            }
            if inconsistent.is_none() && previous < failed {
                for &unit in &units[previous..failed] {
                    self.learned_unit(unit);
                }
                if self
                    .propagate_trail(Propagation::Probing, None, Flush::Trail)
                    .is_some()
                {
                    break;
                }
            }
            if inconsistent.is_some() || candidates.is_empty() {
                break;
            }
        }
        if let Some(unit) = inconsistent {
            if !self.inconsistent {
                self.learned_unit(unit);
                let _ = self.propagate_trail(Propagation::Probing, None, Flush::Trail);
            }
        }
        if !self.inconsistent {
            self.keep_backbone_candidates(&candidates);
        }
    }

    pub(crate) fn binary_clauses_backbone(&mut self) {
        if self.inconsistent || self.option(Opt::Backbone) == 0 || self.terminated() {
            return;
        }
        self.statistics.backbone_computations += 1;
        self.compute_backbone();
    }
}
