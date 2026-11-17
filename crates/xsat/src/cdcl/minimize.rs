use crate::{
    options::Opt,
    solver::{idx, not, Mark, Reason, Solver},
    store::{
        arena::Ref,
        convert::{narrow, widen},
    },
};

const REMOVED: u32 = u32::MAX;
const SHRINK_LARGE: i32 = 1;
const SHRINK_MINIMIZING: i32 = 2;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Verdict {
    Kept,
    Removable,
    Open,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Minimizing {
    Clause,
    Literal,
}

impl Solver {
    fn mark(&mut self, idx: u32, mark: Mark) {
        self.assignment.assigned[widen(idx)].marks.set(mark);
        self.analysis.marked(mark).push(idx);
    }

    fn marked(&self, idx: u32, mark: Mark) -> bool {
        self.assignment.assigned[widen(idx)].marks.has(mark)
    }

    fn unmark_all(&mut self, mark: Mark) {
        let marked = self.analysis.marked(mark);
        for &idx in marked.iter() {
            self.assignment.assigned[widen(idx)].marks.clear(mark);
        }
        marked.clear();
    }

    pub(crate) fn reset_removable(&mut self) {
        self.unmark_all(Mark::Removable);
    }

    pub(crate) fn sort_deduced_clause(&mut self) {
        self.analysis.levels.sort_unstable();
        let mut position = 1;
        for &level in self.analysis.levels.iter().rev() {
            let frame = &mut self.assignment.frames[widen(level)];
            let used = frame.used;
            frame.used = position;
            position += used;
        }
        let mut shadow = std::mem::take(&mut self.analysis.shadow);
        shadow.resize(self.clause.len(), REMOVED);
        shadow[0] = self.clause[0];
        for &lit in &self.clause[1..] {
            let frame =
                &mut self.assignment.frames[widen(self.assignment.assigned[widen(idx(lit))].level)];
            shadow[widen(frame.used)] = lit;
            frame.used += 1;
        }
        std::mem::swap(&mut self.clause, &mut shadow);
        shadow.clear();
        self.analysis.shadow = shadow;
        let mut position = 1;
        for &level in self.analysis.levels.iter().rev() {
            let frame = &mut self.assignment.frames[widen(level)];
            let end = frame.used;
            frame.used = end - position;
            position = end;
        }
    }

    fn minimized_index(&self, minimizing: Minimizing, idx: u32, depth: u32) -> Verdict {
        let assigned = self.assignment.assigned[widen(idx)];
        if assigned.level == 0 || assigned.marks.has(Mark::Removable) && depth > 0 {
            return Verdict::Removable;
        }
        if assigned.reason() == Reason::Decision || assigned.marks.has(Mark::Poisoned) {
            return Verdict::Kept;
        }
        if (minimizing == Minimizing::Clause || depth == 0)
            && self.assignment.frames[widen(assigned.level)].used <= 1
        {
            return Verdict::Kept;
        }
        Verdict::Open
    }

    fn minimize_reference(
        &mut self,
        minimizing: Minimizing,
        at: Ref,
        lit: u32,
        depth: u32,
    ) -> bool {
        let next_depth = depth.saturating_add(1);
        if self.option(Opt::Minimizeticks) != 0 {
            self.statistics.search_ticks += 1;
        }
        for position in 0..self.clauses.arena.size(at) {
            let other = self.clauses.arena.lit(at, position);
            if other != not(lit) && !self.minimize_literal(minimizing, other, next_depth) {
                return false;
            }
        }
        true
    }

    fn minimize_binary(&mut self, minimizing: Minimizing, lit: u32, depth: u32) -> bool {
        let saved = self.analysis.minimize.len();
        let mut next = lit;
        let res = loop {
            let next_idx = idx(next);
            match self.minimized_index(minimizing, next_idx, 1) {
                Verdict::Removable => break true,
                Verdict::Kept => break false,
                Verdict::Open => {}
            }
            self.analysis.minimize.push(next_idx);
            match self.assignment.assigned[widen(next_idx)].reason() {
                Reason::Binary(other) => next = other,
                Reason::Clause(at) => {
                    break self.minimize_reference(minimizing, at, next, depth.saturating_add(1));
                }
                Reason::Decision | Reason::Unit => break false,
            }
        };
        let mark = if res { Mark::Removable } else { Mark::Poisoned };
        for position in saved..self.analysis.minimize.len() {
            self.mark(self.analysis.minimize[position], mark);
        }
        self.analysis.minimize.truncate(saved);
        res
    }

    fn minimize_literal(&mut self, minimizing: Minimizing, lit: u32, depth: u32) -> bool {
        let depth_limit = u32::try_from(self.option(Opt::Minimizedepth)).unwrap_or(0);
        if depth >= depth_limit {
            return false;
        }
        let lit_idx = idx(lit);
        match self.minimized_index(minimizing, lit_idx, depth) {
            Verdict::Removable => return true,
            Verdict::Kept => return false,
            Verdict::Open => {}
        }
        let res = match self.assignment.assigned[widen(lit_idx)].reason() {
            Reason::Binary(other) => self.minimize_binary(minimizing, other, depth),
            Reason::Clause(at) => self.minimize_reference(minimizing, at, lit, depth),
            Reason::Decision | Reason::Unit => false,
        };
        if depth == 0 {
            return res;
        }
        if !res {
            self.mark(lit_idx, Mark::Poisoned);
        } else if !self.marked(lit_idx, Mark::Removable) {
            self.mark(lit_idx, Mark::Removable);
        }
        res
    }

    fn compact_clause(&mut self) {
        self.clause.retain(|&lit| lit != REMOVED);
    }

    pub(crate) fn minimize_clause(&mut self) {
        for position in 0..self.clause.len() {
            self.mark(idx(self.clause[position]), Mark::Removable);
        }
        if self.option(Opt::Shrink) > SHRINK_MINIMIZING {
            return;
        }
        for position in (1..self.clause.len()).rev() {
            if self.minimize_literal(Minimizing::Clause, self.clause[position], 0) {
                self.clause[position] = REMOVED;
            }
        }
        self.compact_clause();
        self.unmark_all(Mark::Poisoned);
    }

    fn shrink_literal(&mut self, level: u32, lit: u32) -> Verdict {
        let lit_idx = idx(lit);
        let assigned = self.assignment.assigned[widen(lit_idx)];
        if assigned.level == 0 || assigned.marks.has(Mark::Shrinkable) {
            return Verdict::Removable;
        }
        if assigned.level < level {
            if assigned.marks.has(Mark::Removable) {
                return Verdict::Removable;
            }
            if self.option(Opt::Shrink) > SHRINK_MINIMIZING
                && self.minimize_literal(Minimizing::Literal, lit, 1)
            {
                return Verdict::Removable;
            }
            return Verdict::Kept;
        }
        self.mark(lit_idx, Mark::Shrinkable);
        Verdict::Open
    }

    fn shrink_along_reason(&mut self, level: u32, uip: u32) -> Option<u32> {
        match self.assignment.assigned[widen(idx(uip))].reason() {
            Reason::Binary(other) => Some(u32::from(
                self.shrink_literal(level, other) == Verdict::Open,
            )),
            Reason::Clause(at) if self.option(Opt::Shrink) > SHRINK_LARGE => {
                if self.option(Opt::Minimizeticks) != 0 {
                    self.statistics.search_ticks += 1;
                }
                let mut open = 0;
                for position in 0..self.clauses.arena.size(at) {
                    let other = self.clauses.arena.lit(at, position);
                    if other == uip {
                        continue;
                    }
                    match self.shrink_literal(level, other) {
                        Verdict::Kept => return None,
                        Verdict::Open => open += 1,
                        Verdict::Removable => {}
                    }
                }
                Some(open)
            }
            Reason::Clause(_) | Reason::Decision | Reason::Unit => None,
        }
    }

    fn shrink_block(&mut self, begin: usize, end: usize, level: u32, max_trail: u32) -> u32 {
        let mut open = narrow(end - begin);
        for position in begin..end {
            let lit = self.clause[position];
            if lit != REMOVED {
                let _ = self.shrink_literal(level, lit);
            }
        }
        let mut t = widen(max_trail);
        let uip = loop {
            let uip = loop {
                let uip = self.assignment.trail[t];
                t = t.saturating_sub(1);
                if self.marked(idx(uip), Mark::Shrinkable) {
                    break uip;
                }
            };
            if open == 1 {
                break Some(uip);
            }
            match self.shrink_along_reason(level, uip) {
                Some(opened) => open = open + opened - 1,
                None => break None,
            }
        };
        let Some(uip) = uip else {
            self.unmark_all(Mark::Shrinkable);
            return 0;
        };
        let mut shrunken = 0;
        for position in begin..end {
            if self.clause[position] != REMOVED {
                self.clause[position] = REMOVED;
                shrunken += 1;
            }
        }
        self.clause[begin] = not(uip);
        let uip_idx = idx(uip);
        if !self.assignment.assigned[widen(uip_idx)].analyzed {
            self.assignment.assigned[widen(uip_idx)].analyzed = true;
            self.analysis.analyzed.push(uip_idx);
        }
        while let Some(shrinkable_idx) = self.analysis.marked(Mark::Shrinkable).pop() {
            self.assignment.assigned[widen(shrinkable_idx)]
                .marks
                .clear(Mark::Shrinkable);
            if !self.marked(shrinkable_idx, Mark::Removable) {
                self.mark(shrinkable_idx, Mark::Removable);
            }
        }
        shrunken - 1
    }

    fn next_block(&self, end: usize) -> (usize, u32, u32) {
        let mut level = None;
        let mut max_trail = 0;
        let mut begin = end;
        while begin > 0 {
            let assigned = self.assignment.assigned[widen(idx(self.clause[begin - 1]))];
            if level.is_some_and(|level| assigned.level > level) {
                break;
            }
            level = Some(assigned.level);
            begin -= 1;
            max_trail = max_trail.max(assigned.trail);
        }
        (begin, level.unwrap_or(0), max_trail)
    }

    pub(crate) fn shrink_clause(&mut self) {
        let mut end = self.clause.len();
        while end > 0 {
            let (begin, level, max_trail) = self.next_block(end);
            if end - begin >= 2 && self.shrink_block(begin, end, level, max_trail) == 0 {
                for position in begin..end {
                    if self.minimize_literal(Minimizing::Literal, self.clause[position], 0) {
                        self.clause[position] = REMOVED;
                    }
                }
            }
            end = begin;
        }
        self.compact_clause();
        self.unmark_all(Mark::Poisoned);
    }
}
