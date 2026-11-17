use crate::{
    inprocess::dense::Rewatch,
    options::Opt,
    solver::{idx, literal, negated, not, Solver},
    store::{
        arena::Ref,
        convert::{average, narrow, widen},
        random::Generator,
    },
};

const MAX_WALK_REF: u64 = (1 << 31) - 1;
const CB_VALUES: [(f64, f64); 6] = [
    (0.0, 2.00),
    (3.0, 2.50),
    (4.0, 2.85),
    (5.0, 3.70),
    (6.0, 5.10),
    (7.0, 7.40),
];
const DEFAULT_CB: f64 = 2.0;
const TRAIL_SHARE: u32 = 4;

#[derive(Clone, Copy, Debug)]
enum Tagged {
    Binary(u32),
    Large(Ref),
}

#[derive(Clone, Copy, Debug, Default)]
struct Counter {
    count: u32,
    pos: u32,
}

#[derive(Debug)]
struct Walker {
    best_trail_pos: Option<u32>,
    clauses: u32,
    current: u32,
    initial: u32,
    minimum: u32,
    random: Generator,
    counters: Vec<Counter>,
    binaries: Vec<[u32; 2]>,
    refs: Vec<Tagged>,
    occurrences: Vec<Vec<u32>>,
    table: Vec<f64>,
    epsilon: f64,
    original_values: Vec<i8>,
    best_values: Vec<i8>,
    scores: Vec<f64>,
    lits: Vec<u32>,
    unsat: Vec<u32>,
    trail: Vec<u32>,
    size: f64,
    limit: u64,
    flipped: u64,
}

impl Walker {
    fn push_unsat(&mut self, counter_ref: u32) {
        self.counters[widen(counter_ref)].pos = narrow(self.unsat.len());
        self.unsat.push(counter_ref);
    }

    fn pop_unsat(&mut self, counter_ref: u32, pos: u32) -> bool {
        let other = self.unsat.pop().unwrap_or(counter_ref);
        self.current -= 1;
        if counter_ref == other {
            return false;
        }
        self.counters[widen(other)].pos = pos;
        self.unsat[widen(pos)] = other;
        true
    }

    fn init_score_table(&mut self, walks: u64) {
        let cb = if walks % 2 == 1 {
            fit_cbval(self.size)
        } else {
            DEFAULT_CB
        };
        let base = 1.0 / cb;
        let mut epsilon = 1.0;
        let mut next = 1.0;
        while next != 0.0 {
            epsilon = next;
            self.table.push(epsilon);
            next = epsilon * base;
        }
        self.epsilon = epsilon;
    }

    fn scale_score(&self, breaks: u32) -> f64 {
        self.table
            .get(widen(breaks))
            .copied()
            .unwrap_or(self.epsilon)
    }

    fn save_trail(&mut self, keep: Keep) {
        let best = widen(self.best_trail_pos.unwrap_or(0));
        for &lit in &self.trail[..best] {
            self.best_values[widen(idx(lit))] = if negated(lit) { -1 } else { 1 };
        }
        if keep == Keep::Rest {
            self.trail.drain(..best);
            self.best_trail_pos = Some(0);
        }
    }

    fn push_flipped(&mut self, vars: u32, flipped: u32) {
        let Some(best) = self.best_trail_pos else {
            return;
        };
        if self.trail.len() < widen(vars / TRAIL_SHARE + 1) {
            self.trail.push(flipped);
        } else if best > 0 {
            self.save_trail(Keep::Rest);
            self.trail.push(flipped);
        } else {
            self.trail.clear();
            self.best_trail_pos = None;
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Keep {
    Rest,
    Nothing,
}

fn fit_cbval(size: f64) -> f64 {
    let mut i = 0;
    while i + 2 < CB_VALUES.len() && (CB_VALUES[i].0 > size || CB_VALUES[i + 1].0 < size) {
        i += 1;
    }
    let (x1, y1) = CB_VALUES[i];
    let (x2, y2) = CB_VALUES[i + 1];
    let (dx, dy) = (x2 - x1, y2 - y1);
    dy * (size - x1) / dx + y1
}

impl Solver {
    fn binirr_clauses(&self) -> u64 {
        self.statistics.clauses_binary + self.statistics.clauses_irredundant
    }

    fn walking(&self) -> bool {
        let last = self
            .clauses
            .last_irredundant
            .unwrap_or_else(|| self.clauses.arena.end());
        u64::from(last.0) <= MAX_WALK_REF && self.binirr_clauses() <= MAX_WALK_REF
    }

    fn import_decision_phases(&mut self, walker: &mut Walker) {
        for var in 0..self.vars {
            if !self.active[widen(var)] {
                continue;
            }
            let value = self.decide_phase(var);
            walker.best_values[widen(var)] = value;
            self.assignment.values[widen(literal(var))] = value;
            self.assignment.values[widen(not(literal(var)))] = -value;
        }
    }

    fn connect_binary_counters(&self, walker: &mut Walker) -> u32 {
        let mut counter_ref = 0;
        for binary_ref in 0..walker.binaries.len() {
            let [first, second] = walker.binaries[binary_ref];
            let (first_value, second_value) = (self.value(first), self.value(second));
            if first_value == 0 || second_value == 0 {
                continue;
            }
            walker.refs.push(Tagged::Binary(narrow(binary_ref)));
            walker.occurrences[widen(first)].push(counter_ref);
            walker.occurrences[widen(second)].push(counter_ref);
            let count = u32::from(first_value > 0) + u32::from(second_value > 0);
            walker.counters[widen(counter_ref)].count = count;
            if count == 0 {
                walker.push_unsat(counter_ref);
            }
            counter_ref += 1;
        }
        walker.size += 2.0 * f64::from(counter_ref);
        counter_ref
    }

    fn connect_large_counters(&mut self, walker: &mut Walker, mut counter_ref: u32) {
        let refs: Vec<Ref> = self.clauses.arena.refs().collect();
        for at in refs {
            if self.clauses.last_irredundant.is_some_and(|last| last < at) {
                break;
            }
            if self.clauses.arena.garbage(at) || self.clauses.arena.redundant(at) {
                continue;
            }
            let lits = self.clauses.arena.lits(at);
            if lits
                .iter()
                .any(|&lit| walker.original_values[widen(lit)] > 0)
            {
                self.mark_clause_as_garbage(at);
                continue;
            }
            walker.refs.push(Tagged::Large(at));
            let (mut count, mut size) = (0, 0);
            for &lit in lits {
                let value = self.assignment.values[widen(lit)];
                if value == 0 {
                    continue;
                }
                walker.occurrences[widen(lit)].push(counter_ref);
                size += 1;
                if value > 0 {
                    count += 1;
                }
            }
            walker.counters[widen(counter_ref)].count = count;
            if count == 0 {
                walker.push_unsat(counter_ref);
            }
            counter_ref += 1;
            walker.size += f64::from(size);
        }
    }

    fn init_walker(&mut self, binaries: Vec<[u32; 2]>) -> Walker {
        let clauses = u32::try_from(self.binirr_clauses()).unwrap_or(u32::MAX);
        let lits = 2 * widen(self.vars);
        let original_values = std::mem::replace(&mut self.assignment.values, vec![0; lits]);
        let mut walker = Walker {
            best_trail_pos: Some(0),
            clauses,
            current: 0,
            initial: 0,
            minimum: 0,
            random: Generator(self.random.0 ^ self.statistics.walks),
            counters: vec![Counter::default(); widen(clauses)],
            binaries,
            refs: Vec::new(),
            occurrences: vec![Vec::new(); lits],
            table: Vec::new(),
            epsilon: 0.0,
            original_values,
            best_values: vec![0; widen(self.vars)],
            scores: Vec::new(),
            lits: Vec::new(),
            unsat: Vec::new(),
            trail: Vec::new(),
            size: 0.0,
            limit: 0,
            flipped: 0,
        };
        self.import_decision_phases(&mut walker);
        let counter_ref = self.connect_binary_counters(&mut walker);
        self.connect_large_counters(&mut walker, counter_ref);
        walker.current = narrow(walker.unsat.len());
        walker.initial = walker.current;
        walker.size = average(walker.size, f64::from(walker.clauses));
        walker.minimum = walker.current;
        walker.init_score_table(self.statistics.walks);
        walker.limit = self.effort_limit(Opt::Walkeffort, self.statistics.walk_steps);
        walker
    }

    fn break_value(&mut self, walker: &Walker, lit: u32) -> u32 {
        let occurrences = &walker.occurrences[widen(not(lit))];
        let res = occurrences
            .iter()
            .filter(|&&counter_ref| walker.counters[widen(counter_ref)].count == 1)
            .count();
        self.statistics.walk_steps += 1 + u64::try_from(occurrences.len()).unwrap_or(u64::MAX);
        narrow(res)
    }

    fn pick_literal(&mut self, walker: &mut Walker) -> u32 {
        let pos = walker.flipped % u64::from(walker.current);
        walker.flipped += 1;
        let counter_ref = walker.unsat[usize::try_from(pos).unwrap_or(0)];
        let mut lits = std::mem::take(&mut walker.lits);
        match walker.refs[widen(counter_ref)] {
            Tagged::Binary(binary_ref) => {
                lits.extend_from_slice(&walker.binaries[widen(binary_ref)]);
            }
            Tagged::Large(at) => lits.extend_from_slice(self.clauses.arena.lits(at)),
        }
        let mut sum = 0.0;
        let mut picked = 0;
        for &lit in &lits {
            if self.value(lit) == 0 {
                continue;
            }
            picked = lit;
            let breaks = self.break_value(walker, lit);
            let score = walker.scale_score(breaks);
            walker.scores.push(score);
            sum += score;
        }
        let threshold = sum * walker.random.pick_double();
        sum = 0.0;
        let mut scores = walker.scores.iter();
        for &lit in &lits {
            if self.value(lit) == 0 {
                continue;
            }
            sum += scores.next().copied().unwrap_or(0.0);
            if threshold < sum {
                picked = lit;
                break;
            }
        }
        walker.scores.clear();
        lits.clear();
        walker.lits = lits;
        picked
    }

    fn flip_literal(&mut self, walker: &mut Walker, flip: u32) {
        let value = self.value(flip);
        self.assignment.values[widen(flip)] = -value;
        self.assignment.values[widen(not(flip))] = value;
        let mut steps = 1;
        for position in 0..walker.occurrences[widen(flip)].len() {
            let counter_ref = walker.occurrences[widen(flip)][position];
            steps += 1;
            let counter = &mut walker.counters[widen(counter_ref)];
            counter.count += 1;
            if counter.count > 1 {
                continue;
            }
            let pos = counter.pos;
            if walker.pop_unsat(counter_ref, pos) {
                steps += 1;
            }
        }
        self.statistics.walk_steps += steps;
        let mut steps = 1;
        for position in 0..walker.occurrences[widen(not(flip))].len() {
            let counter_ref = walker.occurrences[widen(not(flip))][position];
            steps += 1;
            let counter = &mut walker.counters[widen(counter_ref)];
            counter.count -= 1;
            if counter.count == 0 {
                walker.push_unsat(counter_ref);
            }
        }
        self.statistics.walk_steps += steps;
        walker.current = narrow(walker.unsat.len());
    }

    fn update_best(&self, walker: &mut Walker) {
        walker.minimum = walker.current;
        if walker.best_trail_pos.is_some() {
            walker.best_trail_pos = Some(narrow(walker.trail.len()));
            return;
        }
        for var in 0..self.vars {
            let value = self.value(literal(var));
            if value != 0 {
                walker.best_values[widen(var)] = value;
            }
        }
        walker.best_trail_pos = Some(0);
    }

    fn local_search_round(&mut self, walker: &mut Walker) {
        while walker.minimum > 0 && walker.limit > self.statistics.walk_steps && !self.terminated()
        {
            walker.flipped += 1;
            let lit = self.pick_literal(walker);
            self.flip_literal(walker, lit);
            walker.push_flipped(self.vars, lit);
            if walker.current < walker.minimum {
                self.update_best(walker);
            }
        }
    }

    fn save_final_minimum(&mut self, walker: &mut Walker) {
        if walker.minimum == walker.initial {
            return;
        }
        if walker.best_trail_pos.is_some_and(|best| best > 0) {
            walker.save_trail(Keep::Nothing);
        }
        self.phases.saved.copy_from_slice(&walker.best_values);
    }

    pub(crate) fn walk(&mut self) {
        if !self.walking() {
            return;
        }
        if self.option(Opt::Warmup) != 0 {
            self.warmup();
        }
        self.statistics.walks += 1;
        let mut binaries = Vec::new();
        self.enter_dense_mode(Some(&mut binaries));
        let mut walker = self.init_walker(binaries);
        self.local_search_round(&mut walker);
        self.save_final_minimum(&mut walker);
        self.assignment.values = std::mem::take(&mut walker.original_values);
        self.resume_sparse_mode(Rewatch::All, &walker.binaries);
    }
}
