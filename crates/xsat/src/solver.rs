use std::cmp::Ordering;

use crate::{
    cdcl::{
        analyze::Analysis,
        kimits::{Delay, Last, Limits},
        phases::Phases,
        reluctant::Reluctant,
        smooth::Averages,
        terminate::Terminator,
    },
    dimacs::MAX_VARIABLE,
    error::SolverError,
    external::propagator::Propagator,
    incremental::{assume::Assumptions, extend::Extension},
    inprocess::{backbone::Watching, eliminate::Elimination, kitten::Kitten, sweep::Sweeping},
    options::{Opt, Options},
    store::{
        arena::{Kind, Ref},
        assign::Assignment,
        clause::Clauses,
        convert::{narrow, percent, real, widen, PER_MILLE},
        flags::{Flag, Flags},
        heap::Heap,
        queue::{Links, Queue},
        random::Generator,
        watch::{self, Head},
    },
    trace::proof::{Proof, Step},
};

pub(crate) const TRUE: i8 = 1;
pub(crate) const FALSE: i8 = -1;
pub(crate) const UNASSIGNED: i8 = 0;

pub(crate) const fn idx(lit: u32) -> u32 {
    lit >> 1
}

pub(crate) const fn not(lit: u32) -> u32 {
    lit ^ 1
}

pub(crate) const fn negated(lit: u32) -> bool {
    lit & 1 != 0
}

pub(crate) const fn literal(idx: u32) -> u32 {
    idx << 1
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Reason {
    Decision,
    Unit,
    Binary(u32),
    Clause(Ref),
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Mark {
    Poisoned,
    Removable,
    Shrinkable,
}

impl Mark {
    const fn bit(self) -> u8 {
        match self {
            Mark::Poisoned => 1,
            Mark::Removable => 2,
            Mark::Shrinkable => 4,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub(crate) struct Marks(u8);

impl Marks {
    pub(crate) const fn has(self, mark: Mark) -> bool {
        self.0 & mark.bit() != 0
    }

    pub(crate) fn set(&mut self, mark: Mark) {
        self.0 |= mark.bit();
    }

    pub(crate) fn clear(&mut self, mark: Mark) {
        self.0 &= !mark.bit();
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum ReasonKind {
    Decision,
    Unit,
    Binary,
    Clause,
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct Assigned {
    pub(crate) level: u32,
    pub(crate) trail: u32,
    payload: u32,
    pub(crate) analyzed: bool,
    pub(crate) marks: Marks,
    kind: ReasonKind,
}

impl Assigned {
    pub(crate) fn new(level: u32, trail: u32, reason: Reason) -> Assigned {
        let mut assigned = Assigned {
            level,
            trail,
            payload: 0,
            analyzed: false,
            marks: Marks::default(),
            kind: ReasonKind::Decision,
        };
        assigned.set_reason(reason);
        assigned
    }

    pub(crate) fn reason(&self) -> Reason {
        match self.kind {
            ReasonKind::Decision => Reason::Decision,
            ReasonKind::Unit => Reason::Unit,
            ReasonKind::Binary => Reason::Binary(self.payload),
            ReasonKind::Clause => Reason::Clause(Ref(self.payload)),
        }
    }

    pub(crate) fn set_reason(&mut self, reason: Reason) {
        (self.kind, self.payload) = match reason {
            Reason::Decision => (ReasonKind::Decision, 0),
            Reason::Unit => (ReasonKind::Unit, 0),
            Reason::Binary(lit) => (ReasonKind::Binary, lit),
            Reason::Clause(at) => (ReasonKind::Clause, at.0),
        };
    }
}

impl Default for Assigned {
    fn default() -> Assigned {
        Assigned::new(0, 0, Reason::Decision)
    }
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct Frame {
    pub(crate) decision: Option<u32>,
    pub(crate) trail: u32,
    pub(crate) used: u32,
    pub(crate) promote: bool,
}

#[derive(Clone, Copy, Debug)]
pub(crate) enum Conflict {
    Binary([u32; 2]),
    Large(Ref),
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Mode {
    Focused,
    Stable,
}

impl Mode {
    pub(crate) const fn index(self) -> usize {
        match self {
            Mode::Focused => 0,
            Mode::Stable => 1,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Binaries {
    Few,
    Many,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Outcome {
    Satisfiable,
    Unsatisfiable,
    Unknown,
}

#[derive(Clone, Copy, Debug, Default)]
pub struct Statistics {
    pub conflicts: u64,
    pub decisions: u64,
    pub propagations: u64,
    pub search_ticks: u64,
    pub(crate) searches: u64,
    pub(crate) variables_activated: u64,
    pub(crate) clauses_binary: u64,
    pub(crate) clauses_irredundant: u64,
    pub(crate) clauses_redundant: u64,
    pub(crate) reductions: u64,
    pub(crate) restarts: u64,
    pub(crate) switched: u64,
    pub(crate) random_sequences: u64,
    pub(crate) rephased: u64,
    pub(crate) reordered: u64,
    pub(crate) walks: u64,
    pub(crate) walk_steps: u64,
    pub(crate) probings: u64,
    pub(crate) probing_ticks: u64,
    pub(crate) backbone_computations: u64,
    pub(crate) backbone_ticks: u64,
    pub(crate) transitive_ticks: u64,
    pub(crate) factorizations: u64,
    pub(crate) factor_ticks: u64,
    pub(crate) literals_factor: u64,
    pub(crate) closures: u64,
    pub(crate) variables_eliminate: u64,
    pub(crate) variables_subsume: u64,
    pub(crate) eliminations: u64,
    pub(crate) eliminate_resolutions: u64,
    pub(crate) forward_steps: u64,
    pub(crate) kitten_ticks: u64,
    pub(crate) sweep_completed: u64,
    pub(crate) sweep_equivalences: u64,
    pub(crate) sweep_units: u64,
}

pub(crate) const MAX_GLUE_USED: u32 = 127;
const GLUE_BUCKETS: usize = 128;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Propagation {
    Search,
    Probing,
    Initially,
    Beyond,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Flush {
    Trail,
    Keep,
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub(crate) enum Lifecycle {
    Fresh,
    Input,
    Solved,
}

#[derive(Clone, Copy, Debug, Default)]
struct Adding {
    literals: u32,
    satisfied: bool,
    trivial: bool,
    shrink: bool,
}

#[derive(Debug)]
pub struct Solver {
    pub(crate) options: Options,
    pub(crate) vars: u32,
    pub(crate) imports: Vec<Option<u32>>,
    pub(crate) exports: Vec<u32>,
    pub(crate) units: Vec<i32>,
    pub(crate) assignment: Assignment,
    pub(crate) active: Vec<bool>,
    pub(crate) marks: Vec<i8>,
    pub(crate) phases: Phases,
    pub(crate) clauses: Clauses,
    pub(crate) active_count: u32,
    pub(crate) unflushed: u32,
    pub(crate) inconsistent: bool,
    pub(crate) probing: bool,
    pub(crate) mode: Mode,
    binaries: Binaries,
    pub(crate) mode_ticks: u64,
    pub(crate) queue: Queue,
    pub(crate) random: Generator,
    pub(crate) randec: u32,
    pub(crate) scores: Heap,
    pub(crate) scinc: f64,
    ticks: u64,
    delayed: Vec<(u32, u32, Ref)>,
    pub(crate) analysis: Analysis,
    pub(crate) assumptions: Assumptions,
    pub(crate) clause: Vec<u32>,
    adding: Adding,
    pub(crate) tier1: [u32; 2],
    pub(crate) tier2: [u32; 2],
    pub(crate) limits: Limits,
    pub(crate) last: Last,
    pub(crate) averages: [Averages; 2],
    pub(crate) reluctant: Reluctant,
    pub(crate) glue_used: [[u64; GLUE_BUCKETS]; 2],
    pub(crate) extend: Vec<Extension>,
    pub(crate) restoring: Vec<u32>,
    pub(crate) extension: Vec<bool>,
    pub(crate) propagator: Option<Box<dyn Propagator>>,
    pub(crate) lifecycle: Lifecycle,
    pub(crate) eliminated: Vec<i8>,
    pub(crate) eliminated_at: Vec<Option<u32>>,
    pub(crate) flags: Vec<Flags>,
    pub(crate) vivify_delay: Delay,
    pub(crate) factor_marked: u64,
    pub(crate) congruence_delay: Delay,
    pub(crate) elimination: Elimination,
    pub(crate) sweeping: Sweeping,
    pub(crate) kitten: Option<Kitten>,
    pub(crate) terminator: Terminator,
    pub(crate) statistics: Statistics,
    pub(crate) proof: Option<Proof>,
    original: Vec<i32>,
}

impl Solver {
    #[must_use]
    pub fn new(options: Options) -> Solver {
        Solver {
            options,
            vars: 0,
            imports: Vec::new(),
            exports: Vec::new(),
            units: Vec::new(),
            assignment: Assignment::default(),
            active: Vec::new(),
            marks: Vec::new(),
            phases: Phases::default(),
            clauses: Clauses::default(),
            active_count: 0,
            unflushed: 0,
            inconsistent: false,
            probing: false,
            mode: Mode::Focused,
            binaries: Binaries::Few,
            mode_ticks: 0,
            queue: Queue::default(),
            random: Generator::default(),
            randec: 0,
            scores: Heap::default(),
            scinc: 1.0,
            ticks: 0,
            delayed: Vec::new(),
            analysis: Analysis::default(),
            assumptions: Assumptions::default(),
            clause: Vec::new(),
            adding: Adding::default(),
            tier1: [0; 2],
            tier2: [0; 2],
            limits: Limits::default(),
            last: Last::default(),
            averages: [Averages::default(); 2],
            reluctant: Reluctant::default(),
            glue_used: [[0; GLUE_BUCKETS]; 2],
            extend: Vec::new(),
            restoring: Vec::new(),
            extension: Vec::new(),
            propagator: None,
            lifecycle: Lifecycle::Fresh,
            eliminated: Vec::new(),
            eliminated_at: Vec::new(),
            flags: Vec::new(),
            vivify_delay: Delay::default(),
            factor_marked: 0,
            congruence_delay: Delay::default(),
            elimination: Elimination::default(),
            sweeping: Sweeping::default(),
            kitten: None,
            terminator: Terminator::default(),
            statistics: Statistics::default(),
            proof: None,
            original: Vec::new(),
        }
    }

    #[must_use]
    pub fn statistics(&self) -> &Statistics {
        &self.statistics
    }

    pub(crate) fn option(&self, opt: Opt) -> i32 {
        self.options.get(opt)
    }

    pub(crate) fn value(&self, lit: u32) -> i8 {
        self.assignment.values[widen(lit)]
    }

    pub(crate) fn level_of(&self, lit: u32) -> u32 {
        self.assignment.assigned[widen(idx(lit))].level
    }

    #[must_use]
    pub fn external_value(&self, elit: i32) -> i32 {
        let value = self.external_variable_value(elit.unsigned_abs());
        match if elit < 0 { -value } else { value } {
            TRUE => elit,
            FALSE => -elit,
            _ => 0,
        }
    }

    pub(crate) fn external_variable_value(&self, eidx: u32) -> i8 {
        let eidx = widen(eidx);
        if let Some(&Some(ilit)) = self.imports.get(eidx) {
            self.value(ilit)
        } else if let Some(&Some(at)) = self.eliminated_at.get(eidx) {
            self.eliminated[widen(at)]
        } else {
            UNASSIGNED
        }
    }

    fn import_index(&mut self, eidx: u32) -> u32 {
        if self.imports.len() <= widen(eidx) {
            self.imports.resize(widen(eidx) + 1, None);
        }
        if let Some(ilit) = self.imports[widen(eidx)] {
            return ilit;
        }
        if let Some(slot) = self.eliminated_at.get_mut(widen(eidx)) {
            if slot.take().is_some() {
                self.restoring.push(eidx);
            }
        }
        let iidx = self.vars;
        self.enlarge(iidx + 1);
        self.exports.push(eidx);
        let ilit = literal(iidx);
        self.imports[widen(eidx)] = Some(ilit);
        ilit
    }

    pub(crate) fn import(&mut self, elit: i32) -> u32 {
        let eidx = elit.unsigned_abs();
        let first = if self.option(Opt::Tumble) == 0 {
            narrow(self.imports.len()).clamp(1, eidx)
        } else {
            eidx
        };
        let mut ilit = 0;
        for other in first..=eidx {
            ilit = self.import_index(other);
        }
        if elit < 0 {
            not(ilit)
        } else {
            ilit
        }
    }

    #[expect(
        clippy::expect_used,
        reason = "internal variables are bounded as in Kissat, so literals fit the 31-bit watch encoding; running out is a resource limit"
    )]
    fn enlarge(&mut self, vars: u32) {
        let vars = Some(vars)
            .filter(|&vars| vars <= MAX_VARIABLE.unsigned_abs())
            .expect("maximum internal variable index exhausted");
        let lits = 2 * widen(vars);
        let vars_size = widen(vars);
        self.assignment.values.resize(lits, UNASSIGNED);
        self.marks.resize(lits, 0);
        self.clauses.watches.resize_with(lits, Vec::new);
        self.assignment
            .assigned
            .resize(vars_size, Assigned::default());
        self.active.resize(vars_size, false);
        self.flags.resize(vars_size, Flags::default());
        self.phases.resize(vars);
        self.queue.links.resize(vars_size, Links::default());
        self.scores.enlarge(vars);
        self.vars = vars;
    }

    pub(crate) fn decrease_size(&mut self, vars: u32) {
        let lits = 2 * widen(vars);
        let vars_size = widen(vars);
        self.assignment.values.truncate(lits);
        self.marks.truncate(lits);
        self.clauses.watches.truncate(lits);
        self.assignment.assigned.truncate(vars_size);
        self.active.truncate(vars_size);
        self.flags.truncate(vars_size);
        self.phases.resize(vars);
        self.queue.links.truncate(vars_size);
        self.exports.truncate(vars_size);
        self.vars = vars;
    }

    pub fn reserve(&mut self, max_var: u32) -> Result<(), SolverError> {
        if max_var > MAX_VARIABLE.unsigned_abs() {
            return Err(SolverError::InvalidMaximumVariable(max_var));
        }
        if self.option(Opt::Tumble) != 0 {
            return Ok(());
        }
        let first = self.vars;
        for eidx in 1..=max_var {
            let _ = self.import_index(eidx);
        }
        for var in first..self.vars {
            self.activate_literal(literal(var));
        }
        Ok(())
    }

    pub(crate) fn input_closed(&self) -> Result<(), SolverError> {
        if self.adding.literals > 0 {
            Err(SolverError::IncompleteClause)
        } else {
            Ok(())
        }
    }

    pub fn add(&mut self, elit: i32) -> Result<(), SolverError> {
        if elit != 0 {
            checked_literal(elit)?;
        }
        if self.lifecycle == Lifecycle::Solved && self.tracing_drat() {
            return Err(SolverError::InputAfterSolveNeedsIdrup);
        }
        self.lifecycle = self.lifecycle.max(Lifecycle::Input);
        self.add_external(elit);
        Ok(())
    }

    pub(crate) fn add_external(&mut self, elit: i32) {
        self.claim_variable(elit);
        if elit == 0 && self.proof.is_some() {
            let input = self.original.clone();
            self.proof_external(Step::Input, &input);
        }
        self.add_literal(elit);
    }

    pub(crate) fn add_literal(&mut self, elit: i32) {
        if self.assignment.level > 0 {
            self.restart_from_root();
        }
        if elit != 0 {
            self.adding.literals += 1;
            if self.proof.is_some() {
                self.original.push(elit);
            }
            let ilit = self.import(elit);
            match (self.marks[widen(ilit)].cmp(&0), self.fixed(ilit).cmp(&0)) {
                (Ordering::Equal, Ordering::Greater) => self.adding.satisfied = true,
                (Ordering::Equal, Ordering::Equal) => {
                    self.marks[widen(ilit)] = TRUE;
                    self.marks[widen(not(ilit))] = FALSE;
                    self.clause.push(ilit);
                }
                (Ordering::Less, _) => self.adding.trivial = true,
                (Ordering::Equal, Ordering::Less) | (Ordering::Greater, _) => {
                    self.adding.shrink = true;
                }
            }
            return;
        }
        if !self.inconsistent && !self.adding.satisfied && !self.adding.trivial {
            for position in 0..self.clause.len() {
                self.activate_literal(self.clause[position]);
            }
            match *self.clause.as_slice() {
                [] => {
                    self.inconsistent = true;
                    self.proof_lits(Step::Add, &[]);
                }
                [unit] => {
                    self.assign(0, unit, Reason::Unit);
                    if self.assignment.level == 0 {
                        let _ = self.search_propagate();
                    }
                }
                _ => {
                    let _ = self.new_clause(Kind::Irredundant, 0);
                }
            }
        }
        if self.proof.is_some() {
            self.trace_original_clause();
        }
        for position in 0..self.clause.len() {
            let lit = self.clause[position];
            self.marks[widen(lit)] = 0;
            self.marks[widen(not(lit))] = 0;
        }
        self.clause.clear();
        self.adding = Adding::default();
        if !self.restoring.is_empty() {
            self.restore_clauses();
        }
    }

    fn trace_original_clause(&mut self) {
        let mut original = std::mem::take(&mut self.original);
        if self.adding.satisfied || self.adding.trivial {
            if original.len() != 1 {
                self.proof_external(Step::Delete, &original);
            }
        } else if !self.inconsistent && self.adding.shrink {
            let lits = std::mem::take(&mut self.clause);
            self.proof_lits(Step::Add, &lits);
            self.clause = lits;
            self.proof_external(Step::Delete, &original);
        }
        original.clear();
        self.original = original;
    }

    pub(crate) fn fixed(&self, lit: u32) -> i8 {
        let value = self.value(lit);
        if value != UNASSIGNED && self.level_of(lit) == 0 {
            value
        } else {
            UNASSIGNED
        }
    }

    pub(crate) fn new_redundant_clause(&mut self, glue: u32) -> Option<Ref> {
        self.new_derived_clause(Kind::Redundant, glue)
    }

    fn new_derived_clause(&mut self, kind: Kind, glue: u32) -> Option<Ref> {
        let at = self.new_clause(kind, glue);
        if self.proof.is_some() {
            let lits = std::mem::take(&mut self.clause);
            self.proof_lits(Step::Add, &lits);
            self.clause = lits;
        }
        at
    }

    pub(crate) fn new_clause(&mut self, kind: Kind, glue: u32) -> Option<Ref> {
        if let [first, second] = *self.clause.as_slice() {
            self.watch_binary(first, second);
            self.count_binary_clause(first, second);
            return None;
        }
        let at = self.clauses.arena.allocate(kind, glue, &self.clause);
        if self.clauses.watching == Watching::Dense {
            self.connect_clause(at);
        } else {
            self.watch_reference(self.clause[0], self.clause[1], at);
        }
        match kind {
            Kind::Redundant => {
                self.clauses.first_reducible.get_or_insert(at);
                self.statistics.clauses_redundant += 1;
            }
            Kind::Irredundant => {
                for position in 0..self.clause.len() {
                    self.mark_added_literal(self.clause[position]);
                }
                self.clauses.last_irredundant = Some(at);
                self.statistics.clauses_irredundant += 1;
            }
        }
        Some(at)
    }

    pub(crate) fn classify(&mut self) {
        let statistics = &self.statistics;
        let clauses = statistics.clauses_binary + statistics.clauses_irredundant;
        self.binaries = if clauses <= u64::from(self.option_u32(Opt::Smallclauses)) {
            Binaries::Few
        } else {
            let fraction = f64::from(self.option(Opt::Bigbigfraction)) / PER_MILLE;
            if percent(statistics.clauses_binary, clauses) >= fraction {
                Binaries::Many
            } else {
                Binaries::Few
            }
        };
    }

    pub(crate) fn mark_clause_as_garbage(&mut self, at: Ref) {
        if self.clauses.arena.redundant(at) {
            self.statistics.clauses_redundant -= 1;
        } else {
            for position in 0..self.clauses.arena.size(at) {
                self.mark_removed_literal(self.clauses.arena.lit(at, position));
            }
            self.statistics.clauses_irredundant -= 1;
        }
        self.proof_clause(Step::Delete, at);
        self.clauses.arena.set_garbage(at);
    }

    pub(crate) fn new_irredundant_clause(&mut self) -> Option<Ref> {
        self.new_derived_clause(Kind::Irredundant, 0)
    }

    pub(crate) fn watch_binary(&mut self, first: u32, second: u32) {
        watch::push_binary(&mut self.clauses.watches[widen(first)], second);
        watch::push_binary(&mut self.clauses.watches[widen(second)], first);
    }

    pub(crate) fn watch_reference(&mut self, first: u32, second: u32, at: Ref) {
        watch::push_blocking(&mut self.clauses.watches[widen(first)], second, at);
        watch::push_blocking(&mut self.clauses.watches[widen(second)], first, at);
    }

    pub(crate) fn activate_literal(&mut self, lit: u32) {
        let idx = idx(lit);
        if self.active[widen(idx)] {
            return;
        }
        self.active[widen(idx)] = true;
        self.active_count += 1;
        self.statistics.variables_activated += 1;
        self.enqueue(idx);
        let score = 1.0 - 1.0 / real(self.statistics.variables_activated);
        self.scores.update(idx, score);
        if self.mode == Mode::Stable && self.value(literal(idx)) == UNASSIGNED {
            self.scores.push(idx);
        }
        self.assignment.unassigned += 1;
        self.mark_removed_literal(literal(idx));
        self.mark_added_literal(literal(idx));
    }

    pub(crate) fn new_binary_clause(&mut self, first: u32, second: u32) {
        self.watch_binary(first, second);
        self.new_unwatched_binary_clause(first, second);
    }

    pub(crate) fn new_unwatched_binary_clause(&mut self, first: u32, second: u32) {
        self.count_binary_clause(first, second);
        self.proof_lits(Step::Add, &[first, second]);
    }

    fn count_binary_clause(&mut self, first: u32, second: u32) {
        self.mark_added_literal(first);
        self.mark_added_literal(second);
        self.statistics.clauses_binary += 1;
    }

    pub(crate) fn fresh_literal(&mut self) -> Option<u32> {
        let eidx = narrow(self.imports.len()).max(1);
        if eidx >= MAX_VARIABLE.unsigned_abs() {
            return None;
        }
        let lit = self.import_index(eidx);
        if self.extension.len() <= widen(eidx) {
            self.extension.resize(widen(eidx) + 1, false);
        }
        self.extension[widen(eidx)] = true;
        self.activate_literal(lit);
        Some(lit)
    }

    pub(crate) fn delete_binary(&mut self, first: u32, second: u32) {
        self.mark_removed_literal(first);
        self.mark_removed_literal(second);
        self.statistics.clauses_binary -= 1;
        self.proof_lits(Step::Delete, &[first, second]);
    }

    pub(crate) fn learned_unit(&mut self, lit: u32) {
        self.assign(0, lit, Reason::Unit);
        self.proof_lits(Step::Add, &[lit]);
    }

    pub(crate) fn deactivate_variable(&mut self, idx: u32) {
        self.active[widen(idx)] = false;
        self.active_count -= 1;
        self.queue.dequeue(idx);
        if self.scores.contains(idx) {
            self.scores.pop(idx);
        }
    }

    fn mark_fixed_literal(&mut self, lit: u32) {
        let idx = idx(lit);
        self.flags[widen(idx)].set(Flag::Fixed);
        self.deactivate_variable(idx);
        self.units.push(self.export_literal(lit));
    }

    #[cold]
    fn assign_root(&mut self, lit: u32, reason: Reason) -> Reason {
        self.mark_fixed_literal(lit);
        self.unflushed += 1;
        if reason != Reason::Unit {
            self.proof_lits(Step::Add, &[lit]);
        }
        Reason::Unit
    }

    #[expect(
        clippy::inline_always,
        reason = "LLVM keeps these out of line under #[inline]; the calls cost 8% of instructions in propagation"
    )]
    #[inline(always)]
    pub(crate) fn assign(&mut self, level: u32, lit: u32, reason: Reason) {
        if let Some(&first) = self.clauses.watches[widen(not(lit))].first() {
            std::hint::black_box(first);
        }
        self.assignment.values[widen(lit)] = TRUE;
        self.assignment.values[widen(not(lit))] = FALSE;
        self.assignment.unassigned -= 1;
        let reason = if level == 0 {
            self.assign_root(lit, reason)
        } else {
            reason
        };
        let trail = narrow(self.assignment.trail.len());
        self.assignment.trail.push(lit);
        let idx = widen(idx(lit));
        if !self.probing {
            self.phases.saved[idx] = if negated(lit) { FALSE } else { TRUE };
        }
        self.assignment.assigned[idx] = Assigned::new(level, trail, reason);
    }

    pub(crate) fn assign_binary(&mut self, lit: u32, other: u32) {
        let assigned = self.assignment.assigned[widen(idx(other))];
        let reason = match assigned.reason() {
            Reason::Binary(jumped) if self.option(Opt::Jumpreasons) != 0 && assigned.level > 0 => {
                jumped
            }
            Reason::Binary(_) | Reason::Clause(_) | Reason::Decision | Reason::Unit => other,
        };
        self.assign(assigned.level, lit, Reason::Binary(reason));
    }

    #[expect(
        clippy::inline_always,
        reason = "LLVM keeps these out of line under #[inline]; the calls cost 8% of instructions in propagation"
    )]
    #[inline(always)]
    pub(crate) fn assign_reference(&mut self, lit: u32, at: Ref) {
        let level = self
            .clauses
            .arena
            .lits(at)
            .iter()
            .filter(|&&other| other != lit)
            .map(|&other| self.assignment.assigned[widen(idx(other))].level)
            .max()
            .unwrap_or(0);
        self.assign(level, lit, Reason::Clause(at));
    }

    pub(crate) fn assign_decision(&mut self, lit: u32) {
        self.assign(self.assignment.level, lit, Reason::Decision);
    }

    pub(crate) fn push_frame(&mut self, decision: u32) {
        self.assignment.frames.push(Frame {
            decision: Some(decision),
            trail: narrow(self.assignment.trail.len()),
            used: 0,
            promote: false,
        });
    }

    pub(crate) fn internal_assume(&mut self, lit: u32) {
        self.assignment.level += 1;
        self.push_frame(lit);
        self.assign_decision(lit);
    }

    #[expect(
        clippy::inline_always,
        reason = "LLVM keeps these out of line under #[inline]; the calls cost 8% of instructions in propagation"
    )]
    #[inline(always)]
    pub(crate) fn propagate_literal(
        &mut self,
        lit: u32,
        kind: Propagation,
        ignore: Option<Ref>,
    ) -> Option<Conflict> {
        let not_lit = not(lit);
        let mut watches = std::mem::take(&mut self.clauses.watches[widen(not_lit)]);
        let slots = watches.as_mut_slice();
        let end = slots.len();
        let mut ticks = 1 + watch::cache_lines(end);
        let assigned = self.assignment.assigned[widen(idx(lit))];
        let level = assigned.level;
        let binary_reason = match assigned.reason() {
            Reason::Binary(jumped)
                if self.binaries == Binaries::Many
                    && level > 0
                    && self.option(Opt::Jumpreasons) != 0 =>
            {
                jumped
            }
            Reason::Binary(_) | Reason::Clause(_) | Reason::Decision | Reason::Unit => not_lit,
        };
        let mut conflict = None;
        let (mut p, mut q) = (0, 0);
        while p < end {
            let head = slots[p];
            slots[q] = head;
            p += 1;
            q += 1;
            match watch::decode(head) {
                Head::Binary(other) => {
                    let other_value = self.value(other);
                    if other_value > 0 {
                        continue;
                    }
                    if other_value < 0 {
                        conflict = Some(Conflict::Binary([not_lit, other]));
                        if kind == Propagation::Beyond {
                            continue;
                        }
                        break;
                    }
                    self.assign(level, other, Reason::Binary(binary_reason));
                    ticks += 1;
                }
                Head::Blocking(blocking) => {
                    let tail = slots[p];
                    slots[q] = tail;
                    p += 1;
                    q += 1;
                    if self.value(blocking) > 0 {
                        continue;
                    }
                    let at = Ref(tail);
                    ticks += 1;
                    let Some(clause) = self
                        .clauses
                        .arena
                        .watched(at)
                        .filter(|clause| !clause.garbage)
                    else {
                        q -= 2;
                        continue;
                    };
                    let lits = clause.lits;
                    let other = lits[0] ^ lits[1] ^ not_lit;
                    let other_value = self.assignment.values[widen(other)];
                    if other_value > 0 {
                        slots[q - 2] = watch::blocking(other);
                        continue;
                    }
                    let found = replacement(lits, &self.assignment.values, widen(*clause.searched));
                    if let Some(position) = found {
                        let replacement = lits[position];
                        lits[0] = other;
                        lits[1] = replacement;
                        lits[position] = not_lit;
                        *clause.searched = narrow(position);
                        self.delayed.push((replacement, other, at));
                        q -= 2;
                        ticks += 1;
                    } else if ignore != Some(at) {
                        if other_value < 0 {
                            conflict = Some(Conflict::Large(at));
                            if kind == Propagation::Beyond {
                                continue;
                            }
                            break;
                        }
                        self.assign_reference(other, at);
                        ticks += 1;
                    }
                }
            }
        }
        self.ticks += ticks;
        if p < end {
            watches.copy_within(p..end, q);
        }
        watches.truncate(q + end - p);
        self.clauses.watches[widen(not_lit)] = watches;
        for (lit, blocking, at) in self.delayed.drain(..) {
            watch::push_blocking(&mut self.clauses.watches[widen(lit)], blocking, at);
        }
        conflict
    }

    pub(crate) fn propagate(&mut self, kind: Propagation) -> Option<Conflict> {
        self.propagate_trail(kind, None, Flush::Trail)
    }

    pub(crate) fn propagate_trail(
        &mut self,
        kind: Propagation,
        ignore: Option<Ref>,
        flush: Flush,
    ) -> Option<Conflict> {
        self.ticks = 0;
        let saved = self.assignment.propagate;
        let mut conflict = None;
        while conflict.is_none() && self.assignment.propagate < self.assignment.trail.len() {
            let lit = self.assignment.trail[self.assignment.propagate];
            self.assignment.propagate += 1;
            conflict = self.propagate_literal(lit, kind, ignore);
        }
        let propagated = u64::try_from(self.assignment.propagate - saved).unwrap_or(u64::MAX);
        self.statistics.propagations += propagated;
        match kind {
            Propagation::Search => self.statistics.search_ticks += self.ticks,
            Propagation::Probing => self.statistics.probing_ticks += self.ticks,
            Propagation::Initially | Propagation::Beyond => {}
        }
        if conflict.is_some() {
            if matches!(kind, Propagation::Search | Propagation::Initially) {
                self.statistics.conflicts += 1;
            }
            if self.assignment.level == 0 && kind != Propagation::Beyond {
                self.inconsistent = true;
                self.proof_lits(Step::Add, &[]);
            }
        } else if flush == Flush::Trail && self.assignment.level == 0 && self.unflushed > 0 {
            self.assignment.trail.clear();
            self.assignment.propagate = 0;
            self.unflushed = 0;
        }
        if kind == Propagation::Search && conflict.is_some() && self.randec > 0 {
            self.randec -= 1;
        }
        conflict
    }

    pub(crate) fn search_propagate(&mut self) -> Option<Conflict> {
        self.propagate(Propagation::Search)
    }

    fn update_target_and_best_phases(&mut self) {
        if self.probing || self.mode == Mode::Focused {
            return;
        }
        self.phases.update(
            self.vars - self.assignment.unassigned,
            &self.assignment.values,
        );
    }

    pub(crate) fn propagate_after_simplifying(&mut self) {
        let kind = if self.probing {
            Propagation::Probing
        } else {
            Propagation::Search
        };
        let _ = self.propagate(kind);
    }

    pub(crate) fn backtrack_propagate_and_flush_trail(&mut self) {
        if self.assignment.level > 0 {
            self.backtrack_in_consistent_state(0);
            self.propagate_after_simplifying();
        }
    }

    pub(crate) fn backtrack_without_updating_phases(&mut self, new_level: u32) {
        if self.assignment.level == new_level {
            return;
        }
        let new_frames = widen(new_level) + 1;
        let new_end = widen(self.assignment.frames[new_frames].trail);
        self.assignment.frames.truncate(new_frames);
        match self.mode {
            Mode::Stable => {
                let scores = &mut self.scores;
                self.assignment.unassign_above(new_end, new_level, |idx| {
                    if !scores.contains(idx) {
                        scores.push(idx);
                    }
                });
            }
            Mode::Focused => {
                let queue = &mut self.queue;
                self.assignment.unassign_above(new_end, new_level, |idx| {
                    if queue.links[widen(idx)].stamp > queue.search_stamp {
                        queue.update(idx);
                    }
                });
            }
        }
        self.assignment.level = new_level;
        self.assignment.propagate = new_end;
    }

    pub(crate) fn backtrack_in_consistent_state(&mut self, new_level: u32) {
        self.update_target_and_best_phases();
        self.backtrack_without_updating_phases(new_level);
    }

    pub(crate) fn backtrack_after_conflict(&mut self, new_level: u32) {
        if self.assignment.level > 0 {
            self.backtrack_without_updating_phases(self.assignment.level - 1);
        }
        self.update_target_and_best_phases();
        self.backtrack_without_updating_phases(new_level);
    }
}

pub(crate) fn checked_literal(elit: i32) -> Result<i32, SolverError> {
    if elit == 0 || elit == i32::MIN || elit.unsigned_abs() > MAX_VARIABLE.unsigned_abs() {
        Err(SolverError::InvalidLiteral(elit))
    } else {
        Ok(elit)
    }
}

fn replacement(lits: &[u32], values: &[i8], searched: usize) -> Option<usize> {
    let free = |lit: &u32| values[widen(*lit)] >= 0;
    lits.get(searched..)
        .and_then(|tail| tail.iter().position(free))
        .map(|offset| searched + offset)
        .or_else(|| {
            lits.get(2..searched)
                .and_then(|head| head.iter().position(free))
                .map(|offset| 2 + offset)
        })
}
