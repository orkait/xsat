use crate::{
    cdcl::kimits::Delay,
    options::Opt,
    solver::{idx, not, Conflict, Mark, Mode, Outcome, Reason, Solver, MAX_GLUE_USED},
    store::{
        arena::{Ref, MAX_USED},
        convert::{real, widen},
        watch,
    },
    trace::proof::Step,
};

const MAX_SCORE: f64 = 1e150;
const DECAY_SCALE: f64 = 1e-3;
const MAX_GLUE_INTERVAL: u64 = 1 << 16;

#[derive(Debug, Default)]
pub(crate) struct Analysis {
    pub(crate) analyzed: Vec<u32>,
    pub(crate) ranks: Vec<(u32, u32)>,
    pub(crate) levels: Vec<u32>,
    pub(crate) shadow: Vec<u32>,
    pub(crate) promote: Vec<u32>,
    pub(crate) minimize: Vec<u32>,
    pub(crate) antecedent_size: u32,
    pub(crate) resolvent_size: u32,
    pub(crate) bumpreasons: Delay,
    poisoned: Vec<u32>,
    removable: Vec<u32>,
    shrinkable: Vec<u32>,
}

impl Analysis {
    pub(crate) fn marked(&mut self, mark: Mark) -> &mut Vec<u32> {
        match mark {
            Mark::Poisoned => &mut self.poisoned,
            Mark::Removable => &mut self.removable,
            Mark::Shrinkable => &mut self.shrinkable,
        }
    }
}

#[derive(Clone, Copy, Debug)]
enum Level {
    Forced,
    Conflict(u32),
}

impl Solver {
    fn conflict_size(&self, conflict: Conflict) -> u32 {
        match conflict {
            Conflict::Binary(_) => 2,
            Conflict::Large(at) => self.clauses.arena.size(at),
        }
    }

    fn conflict_lit(&self, conflict: Conflict, position: u32) -> u32 {
        match conflict {
            Conflict::Binary(lits) => lits[widen(position)],
            Conflict::Large(at) => self.clauses.arena.lit(at, position),
        }
    }

    pub(crate) fn push_analyzed(&mut self, idx: u32) {
        self.assignment.assigned[widen(idx)].analyzed = true;
        self.analysis.analyzed.push(idx);
    }

    pub(crate) fn clear_analyzed(&mut self) {
        for &idx in &self.analysis.analyzed {
            self.assignment.assigned[widen(idx)].analyzed = false;
        }
        self.analysis.analyzed.clear();
    }

    fn determine_new_level(&self, jump: u32) -> u32 {
        let back = self.assignment.level - 1;
        let delta = back - jump;
        let limit = if self.option(Opt::Chrono) == 0 {
            u32::MAX
        } else {
            u32::try_from(self.option(Opt::Chronolevels)).unwrap_or(u32::MAX)
        };
        if delta > limit {
            back
        } else {
            jump
        }
    }

    fn one_literal_on_conflict_level(&mut self, conflict: Conflict) -> Level {
        let size = self.conflict_size(conflict);
        let mut jump_level: Option<u32> = None;
        let mut conflict_level: Option<u32> = None;
        let mut on_conflict_level = 0;
        let mut forced = 0;
        for position in 0..size {
            let lit = self.conflict_lit(conflict, position);
            let lit_level = self.level_of(lit);
            if conflict_level.is_none_or(|level| level < lit_level) {
                on_conflict_level = 1;
                jump_level = conflict_level;
                conflict_level = Some(lit_level);
                forced = lit;
            } else {
                if jump_level.is_none_or(|level| level < lit_level) {
                    jump_level = Some(lit_level);
                }
                if conflict_level == Some(lit_level) {
                    on_conflict_level += 1;
                }
            }
            if on_conflict_level > 1 && conflict_level == Some(self.assignment.level) {
                break;
            }
        }
        let conflict_level = conflict_level.unwrap_or(0);
        if conflict_level == 0 {
            self.inconsistent = true;
            self.proof_lits(Step::Add, &[]);
            return Level::Conflict(0);
        }
        if conflict_level < self.assignment.level {
            self.backtrack_after_conflict(conflict_level);
        }
        if let Conflict::Large(at) = conflict {
            self.watch_highest_levels(at, conflict_level);
        }
        if on_conflict_level > 1 {
            return Level::Conflict(conflict_level);
        }
        let new_level = self.determine_new_level(jump_level.unwrap_or(0));
        self.backtrack_after_conflict(new_level);
        match conflict {
            Conflict::Binary([first, second]) => {
                self.assign_binary(forced, first ^ second ^ forced);
            }
            Conflict::Large(at) => self.assign_reference(forced, at),
        }
        Level::Forced
    }

    fn watch_highest_levels(&mut self, at: Ref, conflict_level: u32) {
        let size = self.clauses.arena.size(at);
        for position in 0..2 {
            let lit = self.clauses.arena.lit(at, position);
            let mut highest_position = position;
            let mut highest_literal = lit;
            let mut highest_level = self.level_of(lit);
            for other_position in position + 1..size {
                let other = self.clauses.arena.lit(at, other_position);
                let level = self.level_of(other);
                if highest_level >= level {
                    continue;
                }
                highest_literal = other;
                highest_position = other_position;
                highest_level = level;
                if highest_level == conflict_level {
                    break;
                }
            }
            if highest_position == position {
                continue;
            }
            if highest_position > 1 {
                watch::remove_blocking(&mut self.clauses.watches[widen(lit)], at);
            }
            let lits = self.clauses.arena.lits_mut(at);
            lits[widen(highest_position)] = lit;
            lits[widen(position)] = highest_literal;
            let blocking = lits[widen(1 - position)];
            if highest_position > 1 {
                watch::push_blocking(
                    &mut self.clauses.watches[widen(highest_literal)],
                    blocking,
                    at,
                );
            }
        }
    }

    fn analyze_failed_literal(&mut self, conflict: Conflict) {
        let Some(failed) = self.assignment.frames[1].decision else {
            return;
        };
        let not_failed = not(failed);
        let mut units = std::mem::take(&mut self.clause);
        'done: {
            let mut unresolved = 0_u32;
            for position in 0..self.conflict_size(conflict) {
                let lit = self.conflict_lit(conflict, position);
                if lit == not_failed {
                    break 'done;
                }
                if self.level_of(lit) == 0 {
                    continue;
                }
                self.push_analyzed(idx(lit));
                unresolved += 1;
            }
            let mut t = self.assignment.trail.len();
            let mut unit = None;
            loop {
                let lit = loop {
                    t -= 1;
                    let lit = self.assignment.trail[t];
                    if self.assignment.assigned[widen(idx(lit))].analyzed {
                        break lit;
                    }
                };
                if unresolved == 1 {
                    unit = Some(not(lit));
                    units.push(not(lit));
                }
                match self.assignment.assigned[widen(idx(lit))].reason() {
                    Reason::Binary(other) => {
                        if other == not_failed {
                            break 'done;
                        }
                        if !self.assignment.assigned[widen(idx(other))].analyzed {
                            self.push_analyzed(idx(other));
                            unresolved += 1;
                        }
                    }
                    Reason::Clause(at) => {
                        for position in 0..self.clauses.arena.size(at) {
                            let other = self.clauses.arena.lit(at, position);
                            if other == lit || Some(other) == unit {
                                continue;
                            }
                            if other == not_failed {
                                break 'done;
                            }
                            let assigned = self.assignment.assigned[widen(idx(other))];
                            if assigned.level == 0 || assigned.analyzed {
                                continue;
                            }
                            self.push_analyzed(idx(other));
                            unresolved += 1;
                        }
                    }
                    Reason::Decision | Reason::Unit => {}
                }
                unresolved -= 1;
            }
        }
        units.push(not_failed);
        if !self.probing {
            self.update_learned(0);
        }
        self.backtrack_without_updating_phases(0);
        for &unit in &units {
            self.learned_unit(unit);
        }
        units.clear();
        self.clause = units;
        if !self.probing {
            self.assignment.iterating = true;
        }
    }

    fn analyze_literal(&mut self, lit: u32) -> bool {
        let assigned = self.assignment.assigned[widen(idx(lit))];
        if assigned.level == 0 {
            return false;
        }
        self.analysis.antecedent_size += 1;
        if assigned.analyzed {
            return false;
        }
        self.push_analyzed(idx(lit));
        self.analysis.resolvent_size += 1;
        if assigned.level == self.assignment.level {
            return true;
        }
        self.clause.push(lit);
        let frame = &mut self.assignment.frames[widen(assigned.level)];
        frame.used += 1;
        if frame.used == 1 {
            self.analysis.levels.push(assigned.level);
        }
        false
    }

    fn update_learned(&mut self, glue: u32) {
        if self.mode == Mode::Stable {
            self.reluctant.tick();
        }
        let averages = &mut self.averages[self.mode.index()];
        averages.fast_glue.update(f64::from(glue));
        averages.slow_glue.update(f64::from(glue));
    }

    fn update_decision_rate_average(&mut self) {
        let averages = &mut self.averages[self.mode.index()];
        let decisions = self.statistics.decisions - averages.saved_decisions;
        averages.saved_decisions = self.statistics.decisions;
        averages.decision_rate.update(real(decisions));
    }

    fn mark_reason_side_literal(&mut self, lit: u32) {
        let assigned = self.assignment.assigned[widen(idx(lit))];
        if assigned.level > 0 && !assigned.analyzed {
            self.push_analyzed(idx(lit));
        }
    }

    fn analyze_reason_side_literal(&mut self, limit: usize, lit: u32) {
        match self.assignment.assigned[widen(idx(lit))].reason() {
            Reason::Binary(other) => self.mark_reason_side_literal(other),
            Reason::Clause(at) => {
                self.statistics.search_ticks += 1;
                for position in 0..self.clauses.arena.size(at) {
                    let other = self.clauses.arena.lit(at, position);
                    if other != not(lit) {
                        self.mark_reason_side_literal(other);
                        if self.analysis.analyzed.len() > limit {
                            break;
                        }
                    }
                }
            }
            Reason::Decision | Reason::Unit => {}
        }
    }

    fn analyze_reason_side_literals(&mut self) {
        if self.option(Opt::Bump) == 0
            || self.option(Opt::Bumpreasons) == 0
            || self.probing
            || self.analysis.bumpreasons.delaying()
        {
            return;
        }
        let decision_rate = self.averages[self.mode.index()].decision_rate.value;
        if decision_rate >= f64::from(self.option(Opt::Bumpreasonsrate)) {
            return;
        }
        let saved = self.analysis.analyzed.len();
        let limit = widen(self.option_u32(Opt::Bumpreasonslimit)) * saved;
        for position in 0..self.clause.len() {
            self.analyze_reason_side_literal(limit, self.clause[position]);
            if self.analysis.analyzed.len() > limit {
                break;
            }
        }
        if self.analysis.analyzed.len() > limit {
            for &idx in &self.analysis.analyzed[saved..] {
                self.assignment.assigned[widen(idx)].analyzed = false;
            }
            self.analysis.analyzed.truncate(saved);
            self.analysis.bumpreasons.bump();
        } else {
            self.analysis.bumpreasons.reduce();
        }
    }

    pub(crate) fn recompute_glue(&mut self, at: Ref, limit: u32) -> u32 {
        let mut glue = 0;
        for position in 0..self.clauses.arena.size(at) {
            let level = self.level_of(self.clauses.arena.lit(at, position));
            let frame = &mut self.assignment.frames[widen(level)];
            if frame.promote {
                continue;
            }
            glue += 1;
            if glue == limit {
                break;
            }
            frame.promote = true;
            self.analysis.promote.push(level);
        }
        for &level in &self.analysis.promote {
            self.assignment.frames[widen(level)].promote = false;
        }
        self.analysis.promote.clear();
        glue
    }

    fn mark_clause_as_used(&mut self, at: Ref) {
        if !self.clauses.arena.redundant(at) {
            return;
        }
        self.clauses.arena.set_used(at, MAX_USED);
        let old_glue = self.clauses.arena.glue(at);
        let new_glue = self.recompute_glue(at, old_glue);
        if new_glue < old_glue {
            self.promote_clause(at, new_glue);
        }
        let bucket = self.clauses.arena.glue(at).min(MAX_GLUE_USED);
        self.glue_used[self.mode.index()][widen(bucket)] += 1;
    }

    pub(crate) fn promote_clause(&mut self, at: Ref, glue: u32) {
        if self.option(Opt::Promote) != 0 {
            self.clauses.arena.set_glue(at, glue);
        }
    }

    fn deduce_first_uip_clause(&mut self, conflict: Conflict) -> Option<Conflict> {
        if let Conflict::Large(at) = conflict {
            self.mark_clause_as_used(at);
        }
        self.clause.push(0);
        self.analysis.antecedent_size = 0;
        self.analysis.resolvent_size = 0;
        let mut unresolved = 0_u32;
        let mut conflict_size = 0;
        for position in 0..self.conflict_size(conflict) {
            let lit = self.conflict_lit(conflict, position);
            if self.level_of(lit) > 0 {
                conflict_size += 1;
            }
            if self.analyze_literal(lit) {
                unresolved += 1;
            }
        }
        let otfs = self.option(Opt::Otfs) != 0;
        let mut resolved = 0;
        let mut t = self.assignment.trail.len();
        let uip = loop {
            let uip = loop {
                t -= 1;
                let uip = self.assignment.trail[t];
                let assigned = self.assignment.assigned[widen(idx(uip))];
                if assigned.analyzed && assigned.level == self.assignment.level {
                    break uip;
                }
            };
            if unresolved == 1 {
                break uip;
            }
            self.analysis.antecedent_size = 1;
            resolved += 1;
            let reason = self.assignment.assigned[widen(idx(uip))].reason();
            match reason {
                Reason::Binary(other) => {
                    if self.analyze_literal(other) {
                        unresolved += 1;
                    }
                }
                Reason::Clause(at) => {
                    for position in 0..self.clauses.arena.size(at) {
                        let lit = self.clauses.arena.lit(at, position);
                        if lit != uip && self.analyze_literal(lit) {
                            unresolved += 1;
                        }
                    }
                    self.mark_clause_as_used(at);
                }
                Reason::Decision | Reason::Unit => {}
            }
            unresolved -= 1;
            self.analysis.resolvent_size -= 1;
            if let Reason::Clause(at) = reason {
                if otfs
                    && self.analysis.antecedent_size > 2
                    && self.analysis.resolvent_size < self.analysis.antecedent_size
                {
                    let strengthened = self.on_the_fly_strengthen(at, uip);
                    if let Conflict::Large(subsumed) = conflict {
                        if resolved == 1 && self.analysis.resolvent_size < conflict_size {
                            self.on_the_fly_subsume(strengthened, subsumed);
                        }
                    }
                    return Some(strengthened);
                }
            }
        };
        self.clause[0] = not(uip);
        None
    }

    fn learn_clause(&mut self) {
        let not_uip = self.clause[0];
        let glue = u32::try_from(self.analysis.levels.len()).unwrap_or(u32::MAX);
        if !self.probing {
            self.update_learned(glue);
        }
        let learned = match self.clause.len() {
            1 => {
                let new_level = self.determine_new_level(0);
                self.backtrack_after_conflict(new_level);
                self.learned_unit(not_uip);
                if !self.probing {
                    self.assignment.iterating = true;
                }
                None
            }
            2 => {
                let other = self.clause[1];
                let new_level = self.determine_new_level(self.level_of(other));
                self.backtrack_after_conflict(new_level);
                let _ = self.new_redundant_clause(glue);
                self.assign_binary(not_uip, other);
                None
            }
            _ => self.learn_reference(not_uip, glue),
        };
        let eager = widen(self.option_u32(Opt::Eagersubsume));
        if eager > 0 {
            self.eagerly_subsume_last_learned(eager);
            if let Some(at) = learned {
                self.clauses.last_learned[..eager].rotate_right(1);
                self.clauses.last_learned[0] = Some(at);
            }
        }
    }

    fn eagerly_subsume_last_learned(&mut self, eager: usize) {
        for &lit in &self.clause {
            self.marks[widen(lit)] = 1;
        }
        let clause_size = self.clause.len();
        let mut subsumed = false;
        for position in 0..eager {
            let Some(at) = self.clauses.last_learned[position] else {
                continue;
            };
            if self.clauses.arena.garbage(at) || !self.clauses.arena.redundant(at) {
                continue;
            }
            let size = widen(self.clauses.arena.size(at));
            if size <= clause_size {
                continue;
            }
            let mut needed = clause_size;
            let mut remain = size;
            for &lit in self.clauses.arena.lits(at) {
                if self.marks[widen(lit)] != 0 {
                    needed -= 1;
                    if needed == 0 {
                        break;
                    }
                }
                remain -= 1;
                if remain < needed {
                    break;
                }
            }
            if needed > 0 {
                continue;
            }
            self.mark_clause_as_garbage(at);
            self.clauses.last_learned[position] = None;
            subsumed = true;
        }
        for &lit in &self.clause {
            self.marks[widen(lit)] = 0;
        }
        if subsumed {
            self.clauses.last_learned[..eager].sort_by_key(Option::is_none);
        }
    }

    fn learn_reference(&mut self, not_uip: u32, glue: u32) -> Option<Ref> {
        let mut q = 1;
        let mut jump_lit = self.clause[1];
        let mut jump_level = self.level_of(jump_lit);
        let backtrack_level = self.assignment.level - 1;
        for p in 2..self.clause.len() {
            let lit = self.clause[p];
            let level = self.level_of(lit);
            if jump_level >= level {
                continue;
            }
            jump_level = level;
            jump_lit = lit;
            q = p;
            if level == backtrack_level {
                break;
            }
        }
        self.clause[q] = self.clause[1];
        self.clause[1] = jump_lit;
        let at = self.new_redundant_clause(glue);
        if let Some(at) = at {
            self.clauses.arena.set_used(at, MAX_USED);
        }
        let new_level = self.determine_new_level(jump_level);
        self.backtrack_after_conflict(new_level);
        if let Some(at) = at {
            self.assign_reference(not_uip, at);
        }
        at
    }

    fn reset_analysis(&mut self) {
        self.reset_removable();
        for &level in &self.analysis.levels {
            self.assignment.frames[widen(level)].used = 0;
        }
        self.analysis.levels.clear();
        self.clause.clear();
    }

    pub(crate) fn rescale_scores(&mut self) {
        let max_score = self.scores.max_score();
        let rescale = if max_score < self.scinc {
            self.scinc
        } else {
            max_score
        };
        let factor = 1.0 / rescale;
        self.scores.rescale(factor);
        self.scinc *= factor;
    }

    fn bump_analyzed(&mut self) {
        for position in 0..self.analysis.analyzed.len() {
            let idx = self.analysis.analyzed[position];
            if !self.active[widen(idx)] {
                continue;
            }
            let new_score = self.scores.score(idx) + self.scinc;
            self.scores.update(idx, new_score);
            if new_score > MAX_SCORE {
                self.rescale_scores();
            }
        }
        let decay = f64::from(self.option(Opt::Decay)) * DECAY_SCALE;
        self.scinc *= 1.0 / (1.0 - decay);
        if self.scinc > MAX_SCORE {
            self.rescale_scores();
        }
    }

    fn move_analyzed_variables_to_front_of_queue(&mut self) {
        let mut ranks = std::mem::take(&mut self.analysis.ranks);
        ranks.extend(
            self.analysis
                .analyzed
                .iter()
                .map(|&idx| (self.queue.links[widen(idx)].stamp, idx)),
        );
        ranks.sort_unstable();
        for &(_, idx) in &ranks {
            if self.active[widen(idx)] {
                self.move_to_front(idx);
            }
        }
        ranks.clear();
        self.analysis.ranks = ranks;
    }

    pub(crate) fn analyze(&mut self, mut conflict: Conflict) -> Option<Outcome> {
        if self.inconsistent {
            return Some(Outcome::Unsatisfiable);
        }
        if !self.probing {
            self.update_decision_rate_average();
        }
        loop {
            let consistent = match self.one_literal_on_conflict_level(conflict) {
                Level::Forced => Some(true),
                Level::Conflict(0) => Some(false),
                Level::Conflict(1) => {
                    self.analyze_failed_literal(conflict);
                    Some(true)
                }
                Level::Conflict(_) => {
                    if let Some(strengthened) = self.deduce_first_uip_clause(conflict) {
                        self.reset_analysis();
                        self.statistics.conflicts += 1;
                        if self.statistics.conflicts > self.limits.glue_conflicts {
                            self.update_tier_limits();
                        }
                        conflict = strengthened;
                        None
                    } else {
                        if self.option(Opt::Minimize) != 0 {
                            self.sort_deduced_clause();
                            self.minimize_clause();
                            if self.option(Opt::Shrink) != 0 {
                                self.shrink_clause();
                            }
                        }
                        self.analyze_reason_side_literals();
                        self.learn_clause();
                        self.reset_analysis();
                        Some(true)
                    }
                }
            };
            if !self.analysis.analyzed.is_empty() {
                if !self.probing && self.option(Opt::Bump) != 0 {
                    match self.mode {
                        Mode::Stable => self.bump_analyzed(),
                        Mode::Focused => self.move_analyzed_variables_to_front_of_queue(),
                    }
                }
                self.clear_analyzed();
            }
            match consistent {
                Some(true) => return None,
                Some(false) => return Some(Outcome::Unsatisfiable),
                None => {}
            }
        }
    }

    fn update_tier_limits(&mut self) {
        let stable = self.mode.index();
        (self.tier1[stable], self.tier2[stable]) = self.compute_tier_limits(stable);
        if self.limits.glue_interval < MAX_GLUE_INTERVAL {
            self.limits.glue_interval *= 2;
        }
        self.limits.glue_conflicts = self.statistics.conflicts + self.limits.glue_interval;
    }
}
