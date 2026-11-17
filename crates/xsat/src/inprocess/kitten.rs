use crate::{
    cdcl::terminate::Terminator,
    store::{
        convert::{narrow, widen},
        random::Generator,
    },
};

const INVALID: u32 = u32::MAX;
const CORE_FLAG: u32 = 1;
const LEARNED_FLAG: u32 = 2;
const AUX: usize = 0;
const SIZE: usize = 1;
const FLAGS: usize = 2;
const HEADER: usize = 3;
const KATCH_BYTES: usize = 8;
const LINE_SHIFT: u32 = 7;
const PHASE_BLOCK: usize = 64;
const BYTE_BITS: u32 = 8;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Status {
    Unknown,
    Satisfiable,
    Unsatisfiable,
    Core,
}

#[derive(Clone, Copy, Debug, Default)]
struct Kar {
    level: u32,
    reason: u32,
}

#[derive(Clone, Copy, Debug, Default)]
struct Kink {
    next: u32,
    prev: u32,
    stamp: u64,
}

#[derive(Clone, Copy, Debug)]
struct Katch {
    blit: u32,
    reference: u32,
    binary: bool,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Origin {
    Original,
    Learned,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Antecedents {
    Untracked,
    Tracked,
}

#[derive(Clone, Copy, Debug)]
struct Queue {
    first: u32,
    last: u32,
    stamp: u64,
    search: u32,
}

impl Default for Queue {
    fn default() -> Queue {
        Queue {
            first: INVALID,
            last: INVALID,
            stamp: 0,
            search: INVALID,
        }
    }
}

#[derive(Debug)]
pub(crate) struct Kitten {
    status: Status,
    antecedents: Antecedents,
    learned: bool,
    level: u32,
    propagated: usize,
    unassigned: u32,
    inconsistent: u32,
    failing: u32,
    generator: Generator,
    lits: usize,
    evars: usize,
    end_original_ref: usize,
    queue: Queue,
    size: usize,
    vars: Vec<Kar>,
    links: Vec<Kink>,
    marks: Vec<bool>,
    values: Vec<i8>,
    failed: Vec<bool>,
    phases: Vec<u8>,
    import: Vec<u32>,
    watches: Vec<Vec<Katch>>,
    analyzed: Vec<u32>,
    assumptions: Vec<u32>,
    core: Vec<u32>,
    export: Vec<u32>,
    klause: Vec<u32>,
    klauses: Vec<u32>,
    resolved: Vec<u32>,
    trail: Vec<u32>,
    units: Vec<u32>,
    limit: u64,
    initialized: u64,
    ticks: u64,
    terminator: Terminator,
}

impl Kitten {
    pub(crate) fn new(ticks: u64, terminator: Terminator) -> Kitten {
        let mut kitten = Kitten {
            status: Status::Unknown,
            antecedents: Antecedents::Untracked,
            learned: false,
            level: 0,
            propagated: 0,
            unassigned: 0,
            inconsistent: INVALID,
            failing: INVALID,
            generator: Generator::default(),
            lits: 0,
            evars: 0,
            end_original_ref: 0,
            queue: Queue::default(),
            size: 0,
            vars: Vec::new(),
            links: Vec::new(),
            marks: Vec::new(),
            values: Vec::new(),
            failed: Vec::new(),
            phases: Vec::new(),
            import: Vec::new(),
            watches: Vec::new(),
            analyzed: Vec::new(),
            assumptions: Vec::new(),
            core: Vec::new(),
            export: Vec::new(),
            klause: Vec::new(),
            klauses: Vec::new(),
            resolved: Vec::new(),
            trail: Vec::new(),
            units: Vec::new(),
            limit: u64::MAX,
            initialized: 0,
            ticks,
            terminator,
        };
        kitten.initialize();
        kitten
    }

    pub(crate) fn ticks(&self) -> u64 {
        self.ticks
    }

    pub(crate) fn terminated(&self) -> bool {
        self.terminator.terminated()
    }

    fn initialize(&mut self) {
        self.queue = Queue::default();
        self.inconsistent = INVALID;
        self.failing = INVALID;
        self.limit = u64::MAX;
        self.generator = Generator(self.initialized);
        self.initialized += 1;
    }

    pub(crate) fn clear(&mut self) {
        self.assumptions.clear();
        self.core.clear();
        self.klause.clear();
        self.klauses.clear();
        self.trail.clear();
        self.units.clear();
        for watches in &mut self.watches[..self.lits] {
            watches.clear();
        }
        while let Some(eidx) = self.export.pop() {
            self.import[widen(eidx)] = 0;
        }
        self.phases.fill(0);
        self.vars.fill(Kar::default());
        self.values.fill(0);
        self.failed.fill(false);
        self.status = Status::Unknown;
        self.antecedents = Antecedents::Untracked;
        self.learned = false;
        self.level = 0;
        self.propagated = 0;
        self.unassigned = 0;
        self.lits = 0;
        self.evars = 0;
        self.end_original_ref = 0;
        self.initialize();
    }

    pub(crate) fn track_antecedents(&mut self) {
        self.antecedents = Antecedents::Tracked;
    }

    pub(crate) fn set_ticks_limit(&mut self, delta: u64) {
        self.limit = if u64::MAX - delta <= self.ticks {
            u64::MAX
        } else {
            self.ticks + delta
        };
    }

    fn size_of(&self, reference: u32) -> u32 {
        self.klauses[widen(reference) + SIZE]
    }

    fn lit_of(&self, reference: u32, position: u32) -> u32 {
        self.klauses[widen(reference) + HEADER + widen(position)]
    }

    fn flags_of(&self, reference: u32) -> u32 {
        self.klauses[widen(reference) + FLAGS]
    }

    fn learned_klause(&self, reference: u32) -> bool {
        self.flags_of(reference) & LEARNED_FLAG != 0
    }

    fn core_klause(&self, reference: u32) -> bool {
        self.flags_of(reference) & CORE_FLAG != 0
    }

    fn set_core(&mut self, reference: u32) {
        self.klauses[widen(reference) + FLAGS] |= CORE_FLAG;
    }

    fn unset_core(&mut self, reference: u32) {
        self.klauses[widen(reference) + FLAGS] &= !CORE_FLAG;
    }

    fn antecedent_refs(&self, reference: u32) -> &[u32] {
        let start = widen(reference) + HEADER + widen(self.size_of(reference));
        let aux = widen(self.klauses[widen(reference) + AUX]);
        &self.klauses[start..start + aux]
    }

    fn next_klause(&self, reference: u32) -> u32 {
        let mut next = widen(reference) + HEADER + widen(self.size_of(reference));
        if self.antecedents == Antecedents::Tracked && self.learned_klause(reference) {
            next += widen(self.klauses[widen(reference) + AUX]);
        }
        narrow(next)
    }

    fn update_search(&mut self, idx: u32) {
        self.queue.search = idx;
    }

    fn enqueue(&mut self, idx: u32) {
        let last = self.queue.last;
        if last == INVALID {
            self.queue.first = idx;
        } else {
            self.links[widen(last)].next = idx;
        }
        let link = &mut self.links[widen(idx)];
        link.prev = last;
        link.next = INVALID;
        link.stamp = self.queue.stamp;
        self.queue.last = idx;
        self.queue.stamp += 1;
    }

    fn dequeue(&mut self, idx: u32) {
        let Kink { next, prev, .. } = self.links[widen(idx)];
        if prev == INVALID {
            self.queue.first = next;
        } else {
            self.links[widen(prev)].next = next;
        }
        if next == INVALID {
            self.queue.last = prev;
        } else {
            self.links[widen(next)].prev = prev;
        }
    }

    fn enlarge_internal(&mut self, new_lits: usize) {
        let old_lits = self.lits;
        let old_vars = old_lits / 2;
        let new_vars = new_lits / 2;
        if self.size < new_lits {
            let mut new_size = if self.size == 0 { 2 } else { 2 * self.size };
            while new_size <= new_lits {
                new_size *= 2;
            }
            let new_vars_size = new_size / 2;
            self.marks.truncate(old_vars);
            self.marks.resize(new_vars_size, false);
            self.phases.truncate(old_vars);
            self.phases.resize(new_vars_size, 0);
            self.vars.truncate(old_vars);
            self.vars.resize(new_vars_size, Kar::default());
            self.links.truncate(old_vars);
            self.links.resize(new_vars_size, Kink::default());
            self.values.truncate(old_lits);
            self.values.resize(new_size, 0);
            self.failed.truncate(old_lits);
            self.failed.resize(new_size, false);
            self.watches.truncate(old_lits);
            self.watches.resize_with(new_size, Vec::new);
            self.size = new_size;
        }
        self.lits = new_lits;
        for idx in old_vars..new_vars {
            self.unassigned += 1;
            self.enqueue(narrow(idx));
        }
        self.update_search(self.queue.last);
    }

    fn import_literal(&mut self, elit: u32) -> u32 {
        let eidx = widen(elit / 2);
        if eidx >= self.evars {
            if self.import.len() <= eidx {
                let mut new_size = if self.import.is_empty() {
                    1
                } else {
                    2 * self.import.len()
                };
                while new_size <= eidx {
                    new_size *= 2;
                }
                self.import.resize(new_size, 0);
            }
            self.evars = eidx + 1;
        }
        let mut iidx = self.import[eidx];
        if iidx == 0 {
            iidx = narrow(self.export.len());
            self.export.push(narrow(eidx));
            self.import[eidx] = iidx + 1;
        } else {
            iidx -= 1;
        }
        let ilit = 2 * iidx + (elit & 1);
        let new_lits = widen(ilit | 1) + 1;
        if new_lits > self.lits {
            self.enlarge_internal(new_lits);
        }
        ilit
    }

    fn watch_klause(&mut self, lit: u32, reference: u32) {
        let blit = self.lit_of(reference, 0) ^ self.lit_of(reference, 1) ^ lit;
        let binary = self.size_of(reference) == 2;
        self.watches[widen(lit)].push(Katch {
            blit,
            reference,
            binary,
        });
    }

    fn connect_new_klause(&mut self, reference: u32) {
        match self.size_of(reference) {
            0 => {
                if self.inconsistent == INVALID {
                    self.inconsistent = reference;
                }
            }
            1 => self.units.push(reference),
            _ => {
                self.watch_klause(self.lit_of(reference, 0), reference);
                self.watch_klause(self.lit_of(reference, 1), reference);
            }
        }
    }

    #[expect(
        clippy::expect_used,
        reason = "kitten addresses clauses with u32 offsets below INVALID, as in Kissat; running out is a resource limit"
    )]
    fn new_reference(&mut self) -> u32 {
        self.ticks += 1;
        u32::try_from(self.klauses.len())
            .ok()
            .filter(|&reference| reference < INVALID)
            .expect("kitten: maximum number of literals exhausted")
    }

    fn new_original_klause(&mut self, id: u32) {
        let reference = self.new_reference();
        self.klauses.extend([id, narrow(self.klause.len()), 0]);
        self.klauses.extend_from_slice(&self.klause);
        self.connect_new_klause(reference);
        self.end_original_ref = self.klauses.len();
    }

    fn new_learned_klause(&mut self) -> u32 {
        let reference = self.new_reference();
        let aux = match self.antecedents {
            Antecedents::Tracked => self.resolved.len(),
            Antecedents::Untracked => 0,
        };
        self.klauses
            .extend([narrow(aux), narrow(self.klause.len()), LEARNED_FLAG]);
        self.klauses.extend_from_slice(&self.klause);
        if aux > 0 {
            self.klauses.extend_from_slice(&self.resolved);
        }
        self.connect_new_klause(reference);
        self.learned = true;
        reference
    }

    fn assign(&mut self, lit: u32, mut reason: u32) {
        self.values[widen(lit)] = 1;
        self.values[widen(lit ^ 1)] = -1;
        let idx = widen(lit / 2);
        self.phases[idx] = u8::from(lit & 1 != 0);
        self.trail.push(lit);
        self.vars[idx].level = self.level;
        if self.level == 0 && self.size_of(reason) > 1 {
            if self.antecedents == Antecedents::Tracked {
                self.resolved.push(reason);
                for position in 0..self.size_of(reason) {
                    let other = self.lit_of(reason, position);
                    if other != lit {
                        let other_reason = self.vars[widen(other / 2)].reason;
                        self.resolved.push(other_reason);
                    }
                }
            }
            self.klause.push(lit);
            reason = self.new_learned_klause();
            self.resolved.clear();
            self.klause.clear();
        }
        self.vars[idx].reason = reason;
        self.unassigned -= 1;
    }

    fn propagate_literal(&mut self, lit: u32) -> u32 {
        let not_lit = lit ^ 1;
        let mut watches = std::mem::take(&mut self.watches[widen(not_lit)]);
        let end = watches.len();
        let mut ticks = u64::try_from((end * KATCH_BYTES) >> LINE_SHIFT).unwrap_or(0) + 1;
        let mut conflict = INVALID;
        let (mut p, mut q) = (0, 0);
        while p < end {
            let katch = watches[p];
            watches[q] = katch;
            p += 1;
            q += 1;
            let reference = katch.reference;
            let blit_value = self.values[widen(katch.blit)];
            if blit_value > 0 {
                continue;
            }
            if katch.binary {
                if blit_value < 0 {
                    conflict = reference;
                    break;
                }
                self.assign(katch.blit, reference);
                continue;
            }
            let start = widen(reference) + HEADER;
            let size = widen(self.size_of(reference));
            let other = self.klauses[start] ^ self.klauses[start + 1] ^ not_lit;
            let other_value = self.values[widen(other)];
            ticks += 1;
            if other_value > 0 {
                watches[q - 1].blit = other;
                continue;
            }
            let replacement = (start + 2..start + size)
                .find(|&position| self.values[widen(self.klauses[position])] >= 0);
            if let Some(position) = replacement {
                let replacement = self.klauses[position];
                self.klauses[start] = other;
                self.klauses[start + 1] = replacement;
                self.klauses[position] = not_lit;
                self.watch_klause(replacement, reference);
                q -= 1;
            } else if other_value < 0 {
                conflict = reference;
                break;
            } else {
                self.assign(other, reference);
            }
        }
        watches.copy_within(p..end, q);
        watches.truncate(q + end - p);
        self.watches[widen(not_lit)] = watches;
        self.ticks += ticks;
        conflict
    }

    fn propagate(&mut self) -> u32 {
        let mut conflict = INVALID;
        while conflict == INVALID && self.propagated < self.trail.len() {
            let lit = self.trail[self.propagated];
            conflict = self.propagate_literal(lit);
            self.propagated += 1;
        }
        conflict
    }

    fn bump(&mut self) {
        for position in 0..self.analyzed.len() {
            let idx = self.analyzed[position];
            self.marks[widen(idx)] = false;
            if idx != self.queue.last {
                self.dequeue(idx);
                self.enqueue(idx);
            }
        }
    }

    fn unassign(&mut self, lit: u32) {
        self.values[widen(lit)] = 0;
        self.values[widen(lit ^ 1)] = 0;
        self.unassigned += 1;
        let idx = lit / 2;
        let search = self.queue.search;
        if self.links[widen(idx)].stamp > self.links[widen(search)].stamp {
            self.update_search(idx);
        }
    }

    fn backtrack(&mut self, jump: u32) {
        while let Some(&lit) = self.trail.last() {
            if self.vars[widen(lit / 2)].level == jump {
                break;
            }
            self.trail.pop();
            self.unassign(lit);
        }
        self.propagated = self.trail.len();
        self.level = jump;
    }

    fn completely_backtrack_to_root_level(&mut self) {
        let trail = std::mem::take(&mut self.trail);
        for &lit in &trail {
            self.unassign(lit);
        }
        self.trail = trail;
        self.trail.clear();
        for position in 0..self.units.len() {
            let unit = self.lit_of(self.units[position], 0);
            if self.values[widen(unit)] > 0 {
                self.unassign(unit);
            }
        }
        self.propagated = 0;
        self.level = 0;
    }

    fn analyze(&mut self, conflict: u32) {
        self.klause.push(INVALID);
        let mut reason = conflict;
        let level = self.level;
        let mut p = self.trail.len();
        let mut open = 0;
        let mut jump = 0;
        let mut size = 1;
        let uip = loop {
            self.resolved.push(reason);
            for position in 0..self.size_of(reason) {
                let mut lit = self.lit_of(reason, position);
                let idx = lit / 2;
                if self.marks[widen(idx)] {
                    continue;
                }
                self.marks[widen(idx)] = true;
                self.analyzed.push(idx);
                let lit_level = self.vars[widen(idx)].level;
                if lit_level < level {
                    if lit_level > jump {
                        jump = lit_level;
                        if size > 1 {
                            std::mem::swap(&mut self.klause[1], &mut lit);
                        }
                    }
                    self.klause.push(lit);
                    size += 1;
                } else {
                    open += 1;
                }
            }
            let mut uip;
            loop {
                p -= 1;
                uip = self.trail[p];
                if self.marks[widen(uip / 2)] {
                    break;
                }
            }
            open -= 1;
            if open == 0 {
                break uip;
            }
            reason = self.vars[widen(uip / 2)].reason;
        };
        let not_uip = uip ^ 1;
        self.klause[0] = not_uip;
        self.bump();
        self.analyzed.clear();
        let learned = self.new_learned_klause();
        self.resolved.clear();
        self.klause.clear();
        self.backtrack(jump);
        self.assign(not_uip, learned);
    }

    fn failing(&mut self) {
        let mut failed_clashing = INVALID;
        let mut first_failed = INVALID;
        let mut failed_unit = INVALID;
        for &lit in &self.assumptions {
            if self.values[widen(lit)] >= 0 {
                continue;
            }
            if first_failed == INVALID {
                first_failed = lit;
            }
            let var = self.vars[widen(lit / 2)];
            if var.level == 0 {
                failed_unit = lit;
                break;
            }
            if failed_clashing == INVALID && var.reason == INVALID {
                failed_clashing = lit;
            }
        }
        let failed = if failed_unit != INVALID {
            failed_unit
        } else if failed_clashing != INVALID {
            failed_clashing
        } else {
            first_failed
        };
        let failed_idx = failed / 2;
        let failed_reason = self.vars[widen(failed_idx)].reason;
        self.failed[widen(failed)] = true;
        if failed_unit != INVALID {
            self.failing = failed_reason;
            return;
        }
        let not_failed = failed ^ 1;
        if failed_clashing != INVALID {
            self.failed[widen(not_failed)] = true;
            return;
        }
        self.marks[widen(failed_idx)] = true;
        self.analyzed.push(failed_idx);
        self.klause.push(not_failed);
        let mut work = Vec::new();
        let mut p = self.trail.len();
        let mut open = 1;
        while open > 0 {
            open -= 1;
            let mut idx;
            loop {
                p -= 1;
                idx = self.trail[p] / 2;
                if self.marks[widen(idx)] {
                    break;
                }
            }
            let reason = self.vars[widen(idx)].reason;
            if reason == INVALID {
                self.fail_decision(idx);
            } else {
                self.resolved.push(reason);
                for position in 0..self.size_of(reason) {
                    let other = self.lit_of(reason, position);
                    let other_idx = other / 2;
                    if self.marks[widen(other_idx)] {
                        continue;
                    }
                    self.marks[widen(other_idx)] = true;
                    if self.vars[widen(other_idx)].level > 0 {
                        open += 1;
                    } else {
                        work.push(other_idx);
                    }
                    self.analyzed.push(other_idx);
                }
            }
        }
        for idx in work {
            let reason = self.vars[widen(idx)].reason;
            if reason == INVALID {
                self.fail_decision(idx);
            } else {
                self.resolved.push(reason);
            }
        }
        for position in 0..self.analyzed.len() {
            let idx = self.analyzed[position];
            self.marks[widen(idx)] = false;
        }
        self.analyzed.clear();
        self.failing = if let [reason] = *self.resolved.as_slice() {
            reason
        } else {
            self.new_learned_klause()
        };
        self.resolved.clear();
        self.klause.clear();
    }

    fn fail_decision(&mut self, idx: u32) {
        let mut lit = 2 * idx;
        if self.values[widen(lit)] < 0 {
            lit ^= 1;
        }
        self.failed[widen(lit)] = true;
        self.klause.push(lit ^ 1);
    }

    fn decide(&mut self) -> Option<Status> {
        if self.level == 0 && !self.trail.is_empty() {
            self.propagated = 0;
            self.trail.clear();
        }
        let mut decision = INVALID;
        while widen(self.level) < self.assumptions.len() {
            let assumption = self.assumptions[widen(self.level)];
            let value = self.values[widen(assumption)];
            if value < 0 {
                self.failing();
                return Some(Status::Unsatisfiable);
            }
            if value > 0 {
                self.level += 1;
            } else {
                decision = assumption;
                break;
            }
        }
        if self.unassigned == 0 {
            return Some(Status::Satisfiable);
        }
        if self.ticks >= self.limit || self.terminated() {
            return Some(Status::Unknown);
        }
        if decision == INVALID {
            let mut idx = self.queue.search;
            while self.values[widen(2 * idx)] != 0 {
                idx = self.links[widen(idx)].prev;
            }
            self.update_search(idx);
            decision = 2 * idx + u32::from(self.phases[widen(idx)]);
        }
        self.level += 1;
        self.assign(decision, INVALID);
        None
    }

    fn analyze_inconsistent(&mut self, mut reference: u32) {
        if self.antecedents == Antecedents::Untracked {
            self.inconsistent = reference;
            return;
        }
        let mut next = 0;
        loop {
            self.resolved.push(reference);
            for position in 0..self.size_of(reference) {
                let idx = self.lit_of(reference, position) / 2;
                if self.marks[widen(idx)] {
                    continue;
                }
                self.marks[widen(idx)] = true;
                self.analyzed.push(idx);
            }
            let Some(&idx) = self.analyzed.get(next) else {
                break;
            };
            next += 1;
            reference = self.vars[widen(idx)].reason;
        }
        self.inconsistent = self.new_learned_klause();
        for position in 0..self.analyzed.len() {
            let idx = self.analyzed[position];
            self.marks[widen(idx)] = false;
        }
        self.analyzed.clear();
        self.resolved.clear();
    }

    fn propagate_units(&mut self) -> Option<Status> {
        if self.inconsistent != INVALID {
            return Some(Status::Unsatisfiable);
        }
        if self.units.is_empty() {
            return None;
        }
        let mut next = 0;
        while let Some(&reference) = self.units.get(next) {
            next += 1;
            let unit = self.lit_of(reference, 0);
            let value = self.values[widen(unit)];
            if value > 0 {
                continue;
            }
            if value < 0 {
                self.analyze_inconsistent(reference);
                return Some(Status::Unsatisfiable);
            }
            self.assign(unit, reference);
        }
        let conflict = self.propagate();
        if conflict == INVALID {
            return None;
        }
        self.analyze_inconsistent(conflict);
        Some(Status::Unsatisfiable)
    }

    fn reset_core(&mut self) {
        let end = narrow(self.klauses.len());
        let mut reference = 0;
        while reference < end {
            self.unset_core(reference);
            reference = self.next_klause(reference);
        }
        self.core.clear();
    }

    fn reset_assumptions(&mut self) {
        while let Some(assumption) = self.assumptions.pop() {
            self.failed[widen(assumption)] = false;
        }
        self.failing = INVALID;
    }

    fn reset_incremental(&mut self) {
        self.completely_backtrack_to_root_level();
        if !self.assumptions.is_empty() {
            self.reset_assumptions();
        }
        if self.status == Status::Core {
            self.reset_core();
        }
        self.status = Status::Unknown;
    }

    pub(crate) fn clause_with_id_and_exception(&mut self, id: u32, elits: &[u32], except: u32) {
        if self.status != Status::Unknown {
            self.reset_incremental();
        }
        for &elit in elits {
            if elit == except {
                continue;
            }
            let ilit = self.import_literal(elit);
            self.marks[widen(ilit / 2)] = true;
            self.klause.push(ilit);
        }
        for position in 0..self.klause.len() {
            let lit = self.klause[position];
            self.marks[widen(lit / 2)] = false;
        }
        self.new_original_klause(id);
        self.klause.clear();
    }

    pub(crate) fn solve(&mut self) -> Status {
        if self.status == Status::Unknown {
            self.completely_backtrack_to_root_level();
        } else {
            self.reset_incremental();
        }
        let mut res = self.propagate_units();
        while res.is_none() {
            let conflict = self.propagate();
            if conflict == INVALID {
                res = self.decide();
            } else if self.level > 0 {
                self.analyze(conflict);
            } else {
                self.analyze_inconsistent(conflict);
                res = Some(Status::Unsatisfiable);
            }
        }
        let res = res.unwrap_or(Status::Unknown);
        if res == Status::Unknown && !self.assumptions.is_empty() {
            self.reset_assumptions();
        }
        self.status = res;
        res
    }

    pub(crate) fn compute_clausal_core(&mut self) -> u32 {
        let mut original = 0;
        let reason = if self.inconsistent == INVALID {
            self.failing
        } else {
            self.inconsistent
        };
        if reason != INVALID {
            self.resolved.push(reason);
            while let Some(c_ref) = self.resolved.pop() {
                if c_ref == INVALID {
                    let Some(d_ref) = self.resolved.pop() else {
                        break;
                    };
                    self.core.push(d_ref);
                    self.set_core(d_ref);
                    if !self.learned_klause(d_ref) {
                        original += 1;
                    }
                } else {
                    if self.core_klause(c_ref) {
                        continue;
                    }
                    self.resolved.push(c_ref);
                    self.resolved.push(INVALID);
                    if !self.learned_klause(c_ref) {
                        continue;
                    }
                    let antecedents: Vec<u32> = self
                        .antecedent_refs(c_ref)
                        .iter()
                        .copied()
                        .filter(|&d_ref| !self.core_klause(d_ref))
                        .collect();
                    self.resolved.extend(antecedents);
                }
            }
        }
        self.status = Status::Core;
        original
    }

    pub(crate) fn shrink_to_clausal_core(&mut self) {
        self.trail.clear();
        self.unassigned = narrow(self.lits / 2);
        self.propagated = 0;
        self.level = 0;
        self.update_search(self.queue.last);
        self.values[..self.lits].fill(0);
        for watches in &mut self.watches[..self.lits] {
            watches.clear();
        }
        let inconsistent = self.inconsistent;
        if self.learned_klause(inconsistent) || self.size_of(inconsistent) > 0 {
            self.inconsistent = INVALID;
        }
        self.units.clear();
        let end = narrow(self.end_original_ref);
        let mut q = 0;
        let mut c = 0;
        while c < end {
            let next = self.next_klause(c);
            if self.learned_klause(c) || !self.core_klause(c) {
                c = next;
                continue;
            }
            self.unset_core(c);
            match self.size_of(c) {
                0 => {
                    if self.inconsistent == 0 {
                        self.inconsistent = q;
                    }
                }
                1 => self.units.push(q),
                _ => {
                    let (first, second) = (self.lit_of(c, 0), self.lit_of(c, 1));
                    let binary = self.size_of(c) == 2;
                    for (lit, blit) in [(first, second), (second, first)] {
                        self.watches[widen(lit)].push(Katch {
                            blit,
                            reference: q,
                            binary,
                        });
                    }
                }
            }
            self.klauses.copy_within(widen(c)..widen(next), widen(q));
            q += next - c;
            c = next;
        }
        self.klauses.truncate(widen(q));
        self.end_original_ref = self.klauses.len();
        self.core.clear();
        self.status = Status::Unknown;
    }

    pub(crate) fn shuffle_clauses(&mut self) {
        let vars = narrow(self.lits / 2);
        for _ in 0..vars {
            let idx = self.generator.pick(0, vars);
            self.dequeue(idx);
            self.enqueue(idx);
        }
        self.update_search(self.queue.last);
        for lit in 0..self.lits {
            let mut watches = std::mem::take(&mut self.watches[lit]);
            self.shuffle(&mut watches);
            self.watches[lit] = watches;
        }
        let mut units = std::mem::take(&mut self.units);
        self.shuffle(&mut units);
        self.units = units;
    }

    fn shuffle<T>(&mut self, items: &mut [T]) {
        for i in 0..items.len() {
            let j = widen(self.generator.pick(0, narrow(i)));
            if j != i {
                items.swap(i, j);
            }
        }
    }

    pub(crate) fn status(&self) -> Status {
        self.status
    }

    pub(crate) fn assume(&mut self, elit: u32) {
        if self.status != Status::Unknown {
            self.reset_incremental();
        }
        let ilit = self.import_literal(elit);
        self.assumptions.push(ilit);
    }

    pub(crate) fn randomize_phases(&mut self) {
        let vars = self.size / 2;
        let mut random = self.generator.next64();
        let rest = vars & !(PHASE_BLOCK - 1);
        let mut i = 0;
        while i != rest {
            for word in 0..BYTE_BITS {
                for byte in 0..BYTE_BITS {
                    let bit = (random >> (word + BYTE_BITS * byte)) & 1;
                    self.phases[i + widen(word * BYTE_BITS + byte)] = u8::from(bit != 0);
                }
            }
            random = self.generator.next64();
            i += PHASE_BLOCK;
        }
        let mut shift = 0;
        while i != vars {
            self.phases[i] = u8::from((random >> shift) & 1 != 0);
            shift += 1;
            i += 1;
        }
    }

    fn imported(&self, elit: u32) -> Option<u32> {
        let eidx = widen(elit / 2);
        let iidx = *self.import.get(eidx).filter(|_| eidx < self.evars)?;
        (iidx != 0).then(|| 2 * (iidx - 1) + (elit & 1))
    }

    pub(crate) fn value(&self, elit: u32) -> i8 {
        self.imported(elit)
            .map_or(0, |ilit| self.values[widen(ilit)])
    }

    pub(crate) fn fixed(&self, elit: u32) -> i8 {
        self.imported(elit).map_or(0, |ilit| {
            if self.vars[widen(ilit / 2)].level == 0 {
                self.values[widen(ilit)]
            } else {
                0
            }
        })
    }

    pub(crate) fn flip_literal(&mut self, elit: u32) -> bool {
        let Some(ilit) = self.imported(elit) else {
            return false;
        };
        if self.fixed(elit) != 0 {
            return false;
        }
        self.flip(ilit)
    }

    fn flip(&mut self, mut lit: u32) -> bool {
        if self.vars[widen(lit / 2)].level == 0 {
            return false;
        }
        if self.values[widen(lit)] < 0 {
            lit ^= 1;
        }
        let mut watches = std::mem::take(&mut self.watches[widen(lit)]);
        let end = watches.len();
        let mut ticks = u64::try_from((end * KATCH_BYTES) >> LINE_SHIFT).unwrap_or(0) + 1;
        let mut res = true;
        let (mut p, mut q) = (0, 0);
        while p < end {
            let katch = watches[p];
            watches[q] = katch;
            p += 1;
            q += 1;
            if self.values[widen(katch.blit)] > 0 {
                continue;
            }
            let reference = katch.reference;
            let start = widen(reference) + HEADER;
            let size = widen(self.size_of(reference));
            let other = self.klauses[start] ^ self.klauses[start + 1] ^ lit;
            ticks += 1;
            if self.values[widen(other)] > 0 {
                continue;
            }
            let replacement = (start + 2..start + size)
                .find(|&position| self.values[widen(self.klauses[position])] > 0);
            if let Some(position) = replacement {
                let replacement = self.klauses[position];
                self.klauses[start] = other;
                self.klauses[start + 1] = replacement;
                self.klauses[position] = lit;
                self.watch_klause(replacement, reference);
                q -= 1;
            } else {
                res = false;
                break;
            }
        }
        watches.copy_within(p..end, q);
        watches.truncate(q + end - p);
        self.watches[widen(lit)] = watches;
        self.ticks += ticks;
        if res {
            self.values[widen(lit)] = -1;
            self.values[widen(lit ^ 1)] = 1;
        }
        res
    }

    pub(crate) fn core_clauses(&self) -> Vec<(Origin, Vec<u32>)> {
        self.core
            .iter()
            .map(|&reference| {
                let lits = (0..self.size_of(reference))
                    .map(|position| {
                        let ilit = self.lit_of(reference, position);
                        2 * self.export[widen(ilit / 2)] + (ilit & 1)
                    })
                    .collect();
                let origin = if self.learned_klause(reference) {
                    Origin::Learned
                } else {
                    Origin::Original
                };
                (origin, lits)
            })
            .collect()
    }

    pub(crate) fn core_ids(&self) -> Vec<u32> {
        let end = narrow(self.end_original_ref);
        let mut ids = Vec::new();
        let mut reference = 0;
        while reference < end {
            if !self.learned_klause(reference) && self.core_klause(reference) {
                ids.push(self.klauses[widen(reference) + AUX]);
            }
            reference = self.next_klause(reference);
        }
        ids
    }
}
