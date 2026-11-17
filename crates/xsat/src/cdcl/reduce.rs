use crate::{
    options::Opt,
    solver::{idx, Reason, Solver, MAX_GLUE_USED},
    store::{
        arena::{Reason as Marking, Ref, INITIAL_SEARCHED, MAX_USED},
        convert::{real, truncate, widen, PERCENT, PER_MILLE},
        watch::{self, Head},
    },
    trace::proof::Step,
};

const TENTH: f64 = 0.1;
const INITIAL_GLUE_INTERVAL: u64 = 2;
const LOG_OFFSET: f64 = 9.0;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Mapping {
    Identity,
    Compacting,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Satisfied {
    Enough,
    NotEnough,
}

impl Solver {
    pub(crate) fn compute_tier_limits(&self, stable: usize) -> (u32, u32) {
        let used = &self.glue_used[stable];
        let total: u64 = used.iter().sum();
        let mut tier1 = None;
        let mut tier2 = None;
        if total > 0 {
            let relative = |opt| f64::from(self.option(opt)) / PER_MILLE;
            let limit1 = truncate(real(total) * relative(Opt::Tier1relative));
            let limit2 = truncate(real(total) * relative(Opt::Tier2relative));
            let mut accumulated = 0;
            for glue in 0..=MAX_GLUE_USED {
                accumulated += used[widen(glue)];
                if accumulated >= limit1 {
                    tier1 = Some(glue);
                    break;
                }
            }
            if accumulated < limit2 {
                for glue in tier1.map_or(0, |tier1| tier1 + 1)..=MAX_GLUE_USED {
                    accumulated += used[widen(glue)];
                    if accumulated >= limit2 {
                        tier2 = Some(glue);
                        break;
                    }
                }
            }
        }
        if let Some(tier1) = tier1 {
            (tier1, tier2.unwrap_or(tier1))
        } else {
            let tier1 = self.option_u32(Opt::Tier1);
            (tier1, self.option_u32(Opt::Tier2).max(tier1))
        }
    }

    pub(crate) fn option_u32(&self, opt: Opt) -> u32 {
        u32::try_from(self.option(opt)).unwrap_or(0)
    }

    pub(crate) fn init_tiers(&mut self) {
        for stable in 0..2 {
            if self.tier1[stable] == 0 {
                self.tier1[stable] = self.option_u32(Opt::Tier1);
                self.tier2[stable] = self.option_u32(Opt::Tier2).max(self.tier1[stable]);
                if self.limits.glue_interval == 0 {
                    self.limits.glue_interval = INITIAL_GLUE_INTERVAL;
                }
            }
        }
    }

    pub(crate) fn reducing(&self) -> bool {
        self.option(Opt::Reduce) != 0
            && self.statistics.clauses_redundant > 0
            && self.statistics.conflicts >= self.limits.reduce
    }

    fn mark_reasons(&mut self, start: Ref, marking: Marking) {
        for position in 0..self.assignment.trail.len() {
            if let Reason::Clause(at) =
                self.assignment.assigned[widen(idx(self.assignment.trail[position]))].reason()
            {
                if at >= start {
                    self.clauses.arena.set_reason(at, marking);
                }
            }
        }
    }

    fn flush_and_mark_reason_clauses(&mut self, start: Ref) {
        if self.unflushed == 0 {
            self.mark_reasons(start, Marking::Marked);
        } else {
            self.backtrack_propagate_and_flush_trail();
        }
    }

    fn collect_reducibles(&mut self, start: Ref) -> Vec<(u64, Ref)> {
        let end = self.clauses.arena.end();
        let mut at = start;
        while at != end && !self.clauses.arena.redundant(at) {
            at = self.clauses.arena.next(at);
        }
        if at == end {
            self.clauses.first_reducible = None;
            return Vec::new();
        }
        self.clauses.first_reducible = Some(at);
        let tier1 = self.tier1[0];
        let tier2 = tier1.max(self.tier2[1]);
        let mut reducibles = Vec::new();
        while at != end {
            let next = self.clauses.arena.next(at);
            if self.clauses.arena.redundant(at) && !self.clauses.arena.garbage(at) {
                let used = self.clauses.arena.used(at);
                if used > 0 {
                    self.clauses.arena.set_used(at, used - 1);
                }
                let glue = self.clauses.arena.glue(at);
                let kept = self.clauses.arena.reason(at)
                    || glue <= tier1 && used > 0
                    || glue <= tier2 && used >= MAX_USED - 1;
                if !kept {
                    let rank = u64::from(!glue) << 32 | u64::from(!self.clauses.arena.size(at));
                    reducibles.push((rank, at));
                }
            }
            at = next;
        }
        reducibles
    }

    fn mark_less_useful_clauses_as_garbage(&mut self, reducibles: &[(u64, Ref)]) {
        let high = f64::from(self.option(Opt::Reducehigh)) * TENTH;
        let low = f64::from(self.option(Opt::Reducelow)) * TENTH;
        let percent = if low < high {
            high - (high - low) / (real(self.statistics.reductions) + LOG_OFFSET).log10()
        } else {
            low
        };
        let fraction = percent / PERCENT;
        let size = real(u64::try_from(reducibles.len()).unwrap_or(u64::MAX));
        let target = usize::try_from(truncate(size * fraction)).unwrap_or(usize::MAX);
        for &(_, at) in reducibles.iter().take(target) {
            self.mark_clause_as_garbage(at);
        }
    }

    pub(crate) fn reduce(&mut self) {
        self.statistics.reductions += 1;
        let stable = self.mode.index();
        let (tier1, tier2) = self.compute_tier_limits(stable);
        self.tier1[stable] = tier1;
        self.tier2[stable] = tier2;
        let mapping = if self.compacting() {
            Mapping::Compacting
        } else {
            Mapping::Identity
        };
        let start = match mapping {
            Mapping::Compacting => Some(Ref(0)),
            Mapping::Identity => self.clauses.first_reducible,
        };
        if let Some(start) = start {
            self.flush_and_mark_reason_clauses(start);
            let mut reducibles = self.collect_reducibles(start);
            if !reducibles.is_empty() {
                reducibles.sort_by_key(|&(rank, _)| rank);
                self.mark_less_useful_clauses_as_garbage(&reducibles);
                self.sparse_collect(mapping, start);
            } else if mapping == Mapping::Compacting {
                self.sparse_collect(mapping, start);
            } else {
                self.mark_reasons(start, Marking::Unmarked);
            }
        }
        self.classify();
        if !self.inconsistent {
            let interval = real(u64::try_from(self.option(Opt::Reduceint)).unwrap_or(0));
            let delta = truncate(interval * real(self.statistics.reductions).sqrt());
            self.limits.reduce = self.statistics.conflicts + delta;
        }
        self.last.reduce = self.statistics.conflicts;
    }

    fn fixed_value(&self, lit: u32) -> i8 {
        let value = self.value(lit);
        if value != 0 && self.level_of(lit) == 0 {
            value
        } else {
            0
        }
    }

    fn flush_watches(&mut self, lit: u32, mapping: Mapping, start: Ref) {
        let lit_fixed = self.fixed_value(lit);
        let mut watches = std::mem::take(&mut self.clauses.watches[widen(lit)]);
        let (mut p, mut q) = (0, 0);
        while p < watches.len() {
            let head = watches[p];
            p += 1;
            match watch::decode(head) {
                Head::Binary(other) => {
                    let mother = self.mapped(other, mapping);
                    if let (true, Some(mother)) =
                        (lit_fixed <= 0 && self.fixed_value(other) <= 0, mother)
                    {
                        watches[q] = watch::binary(mother);
                        q += 1;
                    } else if lit < other {
                        self.delete_binary(lit, other);
                    }
                }
                Head::Blocking(_) => {
                    let tail = watches[p];
                    p += 1;
                    if lit_fixed == 0 && Ref(tail) < start {
                        watches[q] = head;
                        watches[q + 1] = tail;
                        q += 2;
                    }
                }
            }
        }
        watches.truncate(q);
        let moved = match mapping {
            Mapping::Compacting if lit_fixed == 0 => self.map_literal(lit).unwrap_or(lit),
            Mapping::Compacting | Mapping::Identity => lit,
        };
        self.clauses.watches[widen(moved)] = watches;
    }

    fn mapped(&self, lit: u32, mapping: Mapping) -> Option<u32> {
        match mapping {
            Mapping::Identity => Some(lit),
            Mapping::Compacting => self.map_literal(lit),
        }
    }

    #[expect(
        clippy::too_many_lines,
        reason = "one pass as in collect.c, with the proof lines Kissat writes inside it"
    )]
    fn sweep_garbage_clauses(&mut self, mapping: Mapping, start: Ref) -> Option<Ref> {
        let end = self.clauses.arena.end();
        let first = start;
        let mut src = start;
        let mut dst = start;
        let mut first_reducible = None;
        let mut last_irredundant = if start.0 == 0 {
            None
        } else {
            self.clauses.last_irredundant
        };
        let replaced = |first: Ref| (first.0 != 0).then_some(first);
        let mut removed = Vec::new();
        let mut added = Vec::new();
        while src != end {
            let next = self.clauses.arena.next(src);
            if self.clauses.arena.garbage(src) {
                if last_irredundant == Some(src) {
                    last_irredundant = replaced(first);
                }
                src = next;
                continue;
            }
            let proving = self.proof.is_some();
            removed.clear();
            added.clear();
            if proving {
                removed.extend_from_slice(self.clauses.arena.lits(src));
            }
            let old_size = self.clauses.arena.size(src);
            self.clauses.arena.copy_flags(src, dst);
            let redundant = self.clauses.arena.redundant(src);
            let mut new_size = 0;
            let mut forced = None;
            let mut true_literals = 0;
            let mut other = 0;
            let mut satisfied = false;
            for position in 0..self.clauses.arena.size(src) {
                let lit = self.clauses.arena.lit(src, position);
                let value = self.value(lit);
                let root = value != 0 && self.level_of(lit) == 0;
                if root && value < 0 {
                    continue;
                }
                if root {
                    satisfied = true;
                    break;
                }
                if value > 0 {
                    forced = if true_literals == 0 { Some(lit) } else { None };
                    true_literals += 1;
                } else if value < 0 {
                    other = lit;
                }
                let mlit = self.mapped(lit, mapping).unwrap_or(lit);
                self.clauses.arena.set_lit(dst, new_size, mlit);
                new_size += 1;
                if proving {
                    added.push(lit);
                }
            }
            if satisfied {
                if redundant {
                    self.statistics.clauses_redundant -= 1;
                } else {
                    self.statistics.clauses_irredundant -= 1;
                }
                self.proof_lits(Step::Delete, &removed);
                if last_irredundant == Some(src) {
                    last_irredundant = replaced(first);
                }
                src = next;
                continue;
            }
            let reason = self.clauses.arena.reason(dst);
            if new_size == 2 {
                let (first_lit, second_lit) = (
                    self.clauses.arena.lit(dst, 0),
                    self.clauses.arena.lit(dst, 1),
                );
                self.statistics.clauses_binary += 1;
                if redundant {
                    self.statistics.clauses_redundant -= 1;
                } else {
                    self.statistics.clauses_irredundant -= 1;
                    if last_irredundant == Some(src) {
                        last_irredundant = replaced(first);
                    }
                }
                self.watch_binary(first_lit, second_lit);
                if let (true, Some(forced)) = (reason, forced) {
                    self.assignment.assigned[widen(idx(forced))].set_reason(Reason::Binary(other));
                }
            } else {
                self.clauses.arena.set_size(dst, new_size);
                self.clauses.arena.set_searched(dst, INITIAL_SEARCHED);
                if let (true, Some(forced)) = (reason, forced) {
                    self.assignment.assigned[widen(idx(forced))].set_reason(Reason::Clause(dst));
                    self.clauses.arena.set_reason(dst, Marking::Unmarked);
                }
                if redundant {
                    first_reducible.get_or_insert(dst);
                } else {
                    last_irredundant = Some(dst);
                }
                dst = self.clauses.arena.next(dst);
            }
            if new_size != old_size {
                self.proof_lits(Step::Add, &added);
                self.proof_lits(Step::Delete, &removed);
            }
            src = next;
        }
        self.clauses.first_reducible = first_reducible.filter(|&at| at < dst);
        self.clauses.last_irredundant = last_irredundant.filter(|&at| at < dst);
        self.clauses.last_learned = Default::default();
        self.clauses.arena.truncate(dst);
        first_reducible.filter(|&first| last_irredundant.is_some_and(|last| first < last))
    }

    fn move_redundant_clauses_to_the_end(&mut self, start: Ref) {
        self.mark_reasons(start, Marking::Marked);
        self.clauses.arena.move_redundant_to_end(start);
        let end = self.clauses.arena.end();
        let mut first_reducible = None;
        let mut at = start;
        while at < end {
            if self.clauses.arena.redundant(at) {
                first_reducible.get_or_insert(at);
            } else {
                self.clauses.last_irredundant = Some(at);
            }
            if self.clauses.arena.reason(at) {
                let forced = self
                    .clauses
                    .arena
                    .lits(at)
                    .iter()
                    .copied()
                    .find(|&lit| self.value(lit) > 0);
                if let Some(forced) = forced {
                    self.assignment.assigned[widen(idx(forced))].set_reason(Reason::Clause(at));
                }
                self.clauses.arena.set_reason(at, Marking::Unmarked);
            }
            at = self.clauses.arena.next(at);
        }
        self.clauses.first_reducible = first_reducible;
        self.clauses.last_learned = Default::default();
    }

    fn move_smallest_literal_to_front(&mut self, at: Ref, satisfied: Satisfied, start: u32) -> i8 {
        let size = self.clauses.arena.size(at);
        let front = self.clauses.arena.lit(at, start);
        let mut best_value = self.value(front);
        let enough = |value: i8| value == 0 || value > 0 && satisfied == Satisfied::Enough;
        if enough(best_value) {
            return best_value;
        }
        let level = |solver: &Solver, value: i8, lit: u32| {
            if value == 0 {
                u32::MAX
            } else {
                solver.level_of(lit)
            }
        };
        let mut best_position = start;
        let mut best = front;
        let mut best_level = level(self, best_value, front);
        for position in start + 1..size {
            let lit = self.clauses.arena.lit(at, position);
            let value = self.value(lit);
            if enough(value) {
                best = lit;
                best_position = position;
                best_value = value;
                break;
            }
            let lit_level = level(self, value, lit);
            let better = if best_value < 0 && value > 0 {
                true
            } else if best_value > 0 && value < 0 {
                false
            } else if best_value < 0 {
                best_level < lit_level
            } else {
                best_level > lit_level
            };
            if better {
                best = lit;
                best_position = position;
                best_value = value;
                best_level = lit_level;
            }
        }
        if best_position != start {
            let lits = self.clauses.arena.lits_mut(at);
            lits[widen(start)] = best;
            lits[widen(best_position)] = front;
        }
        best_value
    }

    pub(crate) fn sort_literals(&mut self, at: Ref) {
        let u = self.move_smallest_literal_to_front(at, Satisfied::NotEnough, 0);
        if self.clauses.arena.size(at) > 2 {
            let satisfied = if u >= 0 {
                Satisfied::Enough
            } else {
                Satisfied::NotEnough
            };
            let _ = self.move_smallest_literal_to_front(at, satisfied, 1);
        }
    }

    pub(crate) fn sparse_collect(&mut self, mapping: Mapping, start: Ref) {
        let compacted = match mapping {
            Mapping::Compacting => Some(self.compact_literals()),
            Mapping::Identity => None,
        };
        for lit in 0..2 * self.vars {
            self.flush_watches(lit, mapping, start);
        }
        let moved = self.sweep_garbage_clauses(mapping, start);
        if let Some((vars, mfixed)) = compacted {
            self.finalize_compacting(vars, mfixed);
        }
        if let Some(moved) = moved {
            self.move_redundant_clauses_to_the_end(moved);
        }
        self.watch_large_clauses(start);
    }

    pub(crate) fn watch_large_clauses(&mut self, start: Ref) {
        let end = self.clauses.arena.end();
        let mut at = start;
        while at < end {
            if !self.clauses.arena.garbage(at) {
                self.sort_literals(at);
                self.clauses.arena.set_searched(at, INITIAL_SEARCHED);
                let (first, second) =
                    (self.clauses.arena.lit(at, 0), self.clauses.arena.lit(at, 1));
                self.watch_reference(first, second, at);
            }
            at = self.clauses.arena.next(at);
        }
    }
}
