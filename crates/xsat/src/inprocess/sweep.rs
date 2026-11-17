use crate::{
    cdcl::kimits::Delay,
    inprocess::{
        dense::Rewatch,
        kitten::{Kitten, Origin, Status},
    },
    options::Opt,
    solver::{idx, literal, not, Propagation, Reason, Solver},
    store::{
        arena::{Ref, INITIAL_SEARCHED, INVALID_LIT},
        convert::{average, narrow, real, widen},
        flags::Flag,
        watch::{self, Occurrence},
    },
    trace::proof::Step as ProofStep,
};

const INVALID: u32 = u32::MAX;
const MAX_COMPLETED: u64 = 32;
const MIN_AVERAGE: f64 = 0.001;

#[derive(Debug, Default)]
pub(crate) struct Sweeping {
    pub(crate) schedule: Vec<u32>,
    incomplete: bool,
    delay: Delay,
}

struct Sweeper {
    kitten: Kitten,
    depths: Vec<u32>,
    reprs: Vec<u32>,
    next: Vec<u32>,
    prev: Vec<u32>,
    first: u32,
    last: u32,
    encoded: u32,
    vars: Vec<u32>,
    refs: Vec<Ref>,
    clause: Vec<u32>,
    backbone: Vec<u32>,
    partition: Vec<u32>,
    core: [Vec<u32>; 2],
    ticks: u64,
    clauses: u32,
    depth: u32,
    variables: u32,
}

impl Sweeper {
    fn set_kitten_ticks_limit(&mut self) {
        let remaining = self.ticks.saturating_sub(self.kitten.ticks());
        self.kitten.set_ticks_limit(remaining);
    }

    fn ticks_hit(&self) -> bool {
        self.kitten.ticks() >= self.ticks
    }

    fn repr(&mut self, lit: u32) -> u32 {
        let mut res = lit;
        while self.reprs[widen(res)] != res {
            res = self.reprs[widen(res)];
        }
        if res == lit {
            return res;
        }
        let not_res = not(res);
        let mut prev = lit;
        loop {
            let next = self.reprs[widen(prev)];
            if next == res {
                break;
            }
            self.reprs[widen(not(prev))] = not_res;
            self.reprs[widen(prev)] = res;
            prev = next;
        }
        res
    }

    fn add_literal_to_environment(&mut self, depth: u32, lit: u32) {
        if self.repr(lit) != lit {
            return;
        }
        let idx = idx(lit);
        if self.depths[widen(idx)] != 0 {
            return;
        }
        self.depths[widen(idx)] = depth + 1;
        self.vars.push(idx);
    }

    fn sweep_clause(&mut self, depth: u32) {
        let clause = std::mem::take(&mut self.clause);
        for &lit in &clause {
            self.add_literal_to_environment(depth, lit);
        }
        self.kitten
            .clause_with_id_and_exception(INVALID, &clause, INVALID);
        self.clause = clause;
        self.clause.clear();
        self.encoded += 1;
    }

    fn scheduled(&self, idx: u32) -> bool {
        self.prev[widen(idx)] != INVALID || self.first == idx
    }

    fn schedule_outer(&mut self, idx: u32) {
        let first = self.first;
        if first == INVALID {
            self.last = idx;
        } else {
            self.prev[widen(first)] = idx;
        }
        self.next[widen(idx)] = first;
        self.first = idx;
    }

    fn append(&mut self, idx: u32) {
        let last = self.last;
        if last == INVALID {
            self.first = idx;
        } else {
            self.next[widen(last)] = idx;
        }
        self.prev[widen(idx)] = last;
        self.last = idx;
    }

    fn next_scheduled(&mut self) -> Option<u32> {
        let res = self.last;
        if res == INVALID {
            return None;
        }
        let prev = self.prev[widen(res)];
        self.prev[widen(res)] = INVALID;
        if prev == INVALID {
            self.first = INVALID;
        } else {
            self.next[widen(prev)] = INVALID;
        }
        self.last = prev;
        Some(res)
    }

    fn scheduled_variables(&self) -> Vec<u32> {
        let mut res = Vec::new();
        let mut idx = self.first;
        while idx != INVALID {
            res.push(idx);
            idx = self.next[widen(idx)];
        }
        res
    }

    fn remove(&mut self, lit: u32) {
        let partition = &mut self.partition;
        let Some(p) = partition.iter().position(|&other| other == lit) else {
            return;
        };
        let mut begin = p;
        while begin > 0 && partition[begin - 1] != INVALID_LIT {
            begin -= 1;
        }
        let mut end = p;
        while partition[end] != INVALID_LIT {
            end += 1;
        }
        if end - begin == 2 {
            partition.drain(begin..=end);
        } else {
            partition.remove(p);
        }
    }

    fn flip_backbone_literals(&mut self, max_rounds: u32) {
        if max_rounds == 0 || self.kitten.status() != Status::Satisfiable {
            return;
        }
        let mut round = 0;
        loop {
            round += 1;
            let mut flipped = 0;
            let mut backbone = std::mem::take(&mut self.backbone);
            backbone.retain(|&lit| {
                let flip = self.kitten.flip_literal(lit);
                if flip {
                    flipped += 1;
                }
                !flip
            });
            self.backbone = backbone;
            if self.kitten.terminated()
                || self.kitten.ticks() > self.ticks
                || flipped == 0
                || round >= max_rounds
            {
                break;
            }
        }
    }

    fn flip_partition_literals(&mut self, max_rounds: u32) {
        if max_rounds == 0 || self.kitten.status() != Status::Satisfiable {
            return;
        }
        let mut round = 0;
        loop {
            round += 1;
            let mut flipped = 0;
            let old = std::mem::take(&mut self.partition);
            let mut new = Vec::with_capacity(old.len());
            for class in old
                .split(|&lit| lit == INVALID_LIT)
                .filter(|class| !class.is_empty())
            {
                let start = new.len();
                let mut size = class.len();
                for &lit in class {
                    if self.kitten.flip_literal(lit) {
                        flipped += 1;
                        size -= 1;
                        if size < 2 {
                            break;
                        }
                    } else {
                        new.push(lit);
                    }
                }
                if size > 1 {
                    new.push(INVALID_LIT);
                } else {
                    new.truncate(start);
                }
            }
            self.partition = new;
            if self.kitten.terminated()
                || self.kitten.ticks() > self.ticks
                || flipped == 0
                || round >= max_rounds
            {
                break;
            }
        }
    }
}

impl Solver {
    fn init_sweeper(&mut self) -> Sweeper {
        let mut kitten = Kitten::new(self.statistics.kitten_ticks, self.terminator());
        kitten.track_antecedents();
        self.enter_dense_mode(None);
        self.connect_irredundant_large_clauses();
        let completed = self.statistics.sweep_completed.min(MAX_COMPLETED);
        let capped = |value: u64, max: Opt| {
            u32::try_from(value.min(u64::from(self.option_u32(max)))).unwrap_or(u32::MAX)
        };
        let variables = capped(
            u64::from(self.option_u32(Opt::Sweepvars)) << completed,
            Opt::Sweepmaxvars,
        );
        let depth = capped(
            self.statistics.sweep_completed + u64::from(self.option_u32(Opt::Sweepdepth)),
            Opt::Sweepmaxdepth,
        );
        let clauses = capped(
            u64::from(self.option_u32(Opt::Sweepclauses)) << completed,
            Opt::Sweepmaxclauses,
        );
        let ticks = if self.option(Opt::Sweepcomplete) == 0 {
            self.effort_limit(Opt::Sweepeffort, kitten.ticks())
        } else {
            u64::MAX
        };
        let lits = 2 * widen(self.vars);
        let mut sweeper = Sweeper {
            kitten,
            depths: vec![0; widen(self.vars)],
            reprs: (0..narrow(lits)).collect(),
            next: vec![INVALID; widen(self.vars)],
            prev: vec![INVALID; widen(self.vars)],
            first: INVALID,
            last: INVALID,
            encoded: 0,
            vars: Vec::new(),
            refs: Vec::new(),
            clause: Vec::new(),
            backbone: Vec::new(),
            partition: Vec::new(),
            core: [Vec::new(), Vec::new()],
            ticks,
            clauses,
            depth,
            variables,
        };
        sweeper.set_kitten_ticks_limit();
        sweeper
    }

    fn release_sweeper(&mut self, sweeper: &Sweeper) {
        self.statistics.kitten_ticks = sweeper.kitten.ticks();
        self.resume_sparse_mode(Rewatch::All, &[]);
    }

    fn clear_sweeper(&mut self, sweeper: &mut Sweeper) {
        sweeper.kitten.clear();
        sweeper.kitten.track_antecedents();
        for &idx in &sweeper.vars {
            sweeper.depths[widen(idx)] = 0;
        }
        sweeper.vars.clear();
        for &at in &sweeper.refs {
            self.clauses.arena.clear_swept(at);
        }
        sweeper.refs.clear();
        sweeper.backbone.clear();
        sweeper.partition.clear();
        sweeper.encoded = 0;
        sweeper.set_kitten_ticks_limit();
    }

    fn sweep_binary(&mut self, sweeper: &mut Sweeper, depth: u32, lit: u32, other: u32) {
        if sweeper.repr(lit) != lit || sweeper.repr(other) != other {
            return;
        }
        if self.value(other) > 0 {
            return;
        }
        let other_depth = sweeper.depths[widen(idx(other))];
        let lit_depth = sweeper.depths[widen(idx(lit))];
        if other_depth != 0 && other_depth < lit_depth {
            return;
        }
        sweeper.clause.extend([lit, other]);
        sweeper.sweep_clause(depth);
    }

    fn sweep_reference(&mut self, sweeper: &mut Sweeper, depth: u32, at: Ref) {
        if self.clauses.arena.swept(at) || self.clauses.arena.garbage(at) {
            return;
        }
        for position in 0..self.clauses.arena.size(at) {
            let lit = self.clauses.arena.lit(at, position);
            let value = self.value(lit);
            if value > 0 {
                self.mark_clause_as_garbage(at);
                sweeper.clause.clear();
                return;
            }
            if value == 0 {
                sweeper.clause.push(lit);
            }
        }
        sweeper.refs.push(at);
        self.clauses.arena.set_swept(at);
        sweeper.sweep_clause(depth);
    }

    fn save_core_clause(&self, core: &mut Vec<u32>, origin: Origin, lits: &[u32]) {
        if self.inconsistent {
            return;
        }
        let saved = core.len();
        let mut non_false = 0;
        for &lit in lits {
            let value = self.value(lit);
            if value > 0 {
                core.truncate(saved);
                return;
            }
            core.push(lit);
            if value < 0 {
                continue;
            }
            non_false += 1;
            if origin == Origin::Original && non_false > 1 {
                core.truncate(saved);
                return;
            }
        }
        core.push(INVALID_LIT);
    }

    fn save_core(&mut self, sweeper: &mut Sweeper, core: usize) {
        let _ = sweeper.kitten.compute_clausal_core();
        let mut saved = std::mem::take(&mut sweeper.core[core]);
        for (origin, lits) in sweeper.kitten.core_clauses() {
            self.save_core_clause(&mut saved, origin, &lits);
        }
        sweeper.core[core] = saved;
    }

    fn add_core(&mut self, sweeper: &mut Sweeper, core: usize) {
        if self.inconsistent {
            return;
        }
        let old = std::mem::take(&mut sweeper.core[core]);
        let mut new = Vec::with_capacity(old.len());
        for segment in old.split_inclusive(|&lit| lit == INVALID_LIT) {
            let clause = &segment[..segment.len() - 1];
            let start = new.len();
            let mut satisfied = false;
            let mut unit = INVALID_LIT;
            for &lit in clause {
                let value = self.value(lit);
                if value > 0 {
                    satisfied = true;
                    break;
                }
                if value == 0 {
                    unit = lit;
                    new.push(lit);
                }
            }
            let size = new.len() - start;
            if satisfied || size == 1 {
                new.truncate(start);
            }
            if satisfied {
                continue;
            }
            if size == 0 {
                self.proof_lits(ProofStep::Add, &[]);
                self.inconsistent = true;
                return;
            }
            if size == 1 {
                self.proof_lits(ProofStep::Add, &[unit]);
                self.assign(0, unit, Reason::Unit);
                self.statistics.sweep_units += 1;
                continue;
            }
            self.proof_lits(ProofStep::Add, &new[start..]);
            new.push(INVALID_LIT);
        }
        sweeper.core[core] = new;
    }

    fn clear_core(&mut self, sweeper: &mut Sweeper, core: usize) {
        if self.inconsistent {
            return;
        }
        let saved = std::mem::take(&mut sweeper.core[core]);
        for segment in saved.split_inclusive(|&lit| lit == INVALID_LIT) {
            self.proof_lits(ProofStep::Delete, &segment[..segment.len() - 1]);
        }
        sweeper.core[core] = saved;
        sweeper.core[core].clear();
    }

    fn save_add_clear_core(&mut self, sweeper: &mut Sweeper) {
        self.save_core(sweeper, 0);
        self.add_core(sweeper, 0);
        self.clear_core(sweeper, 0);
    }
}

impl Solver {
    fn init_backbone_and_partition(&self, sweeper: &mut Sweeper) {
        for position in 0..sweeper.vars.len() {
            let idx = sweeper.vars[position];
            if !self.active[widen(idx)] {
                continue;
            }
            let lit = literal(idx);
            let candidate = if sweeper.kitten.value(lit) < 0 {
                not(lit)
            } else {
                lit
            };
            sweeper.backbone.push(candidate);
            sweeper.partition.push(candidate);
        }
        sweeper.partition.push(INVALID_LIT);
    }

    fn sweep_refine_partition(&self, sweeper: &mut Sweeper) {
        let old = std::mem::take(&mut sweeper.partition);
        let mut new = Vec::new();
        for class in old
            .split(|&lit| lit == INVALID_LIT)
            .filter(|class| !class.is_empty())
        {
            for wanted in [1, -1] {
                let start = new.len();
                for &other in class {
                    if sweeper.repr(other) != other || self.value(other) != 0 {
                        continue;
                    }
                    if sweeper.kitten.value(other) == wanted {
                        new.push(other);
                    }
                }
                match new.len() - start {
                    0 => {}
                    1 => new.truncate(start),
                    _ => new.push(INVALID_LIT),
                }
            }
        }
        sweeper.partition = new;
    }

    fn sweep_refine(&self, sweeper: &mut Sweeper) {
        if !sweeper.backbone.is_empty() {
            let mut backbone = std::mem::take(&mut sweeper.backbone);
            backbone.retain(|&lit| self.value(lit) == 0 && sweeper.kitten.value(lit) > 0);
            sweeper.backbone = backbone;
        }
        if !sweeper.partition.is_empty() {
            self.sweep_refine_partition(sweeper);
        }
    }

    fn sweep_solve(sweeper: &mut Sweeper) -> Status {
        sweeper.kitten.randomize_phases();
        sweeper.kitten.solve()
    }

    fn sweep_backbone_candidate(&mut self, sweeper: &mut Sweeper, lit: u32) -> bool {
        if sweeper.kitten.fixed(lit) != 0 {
            return false;
        }
        if sweeper.kitten.status() == Status::Satisfiable && sweeper.kitten.flip_literal(lit) {
            return false;
        }
        sweeper.kitten.assume(not(lit));
        match Solver::sweep_solve(sweeper) {
            Status::Satisfiable => {
                self.sweep_refine(sweeper);
                false
            }
            Status::Unsatisfiable => {
                self.save_add_clear_core(sweeper);
                true
            }
            Status::Unknown | Status::Core => false,
        }
    }

    fn schedule_inner(&self, sweeper: &mut Sweeper, idx: u32) {
        if !self.active[widen(idx)] {
            return;
        }
        let next = sweeper.next[widen(idx)];
        if next != INVALID {
            let prev = sweeper.prev[widen(idx)];
            sweeper.prev[widen(next)] = prev;
            if prev == INVALID {
                sweeper.first = next;
            } else {
                sweeper.next[widen(prev)] = next;
            }
            sweeper.next[widen(idx)] = INVALID;
            sweeper.append(idx);
        } else if sweeper.last != idx {
            sweeper.append(idx);
        }
    }

    fn substitute_watch(&mut self, other: u32, src: u32, dst: u32) {
        if let Some(word) = self.clauses.watches[widen(other)]
            .iter_mut()
            .find(|word| **word == src)
        {
            *word = dst;
        }
    }

    fn substitute_connected_clauses(&mut self, lit: u32, repr: u32) {
        if self.inconsistent || self.value(lit) != 0 || self.value(repr) != 0 {
            return;
        }
        let not_repr = not(repr);
        let mut delayed = Vec::new();
        let mut watches = std::mem::take(&mut self.clauses.watches[widen(lit)]);
        let end = watches.len();
        let (mut p, mut q) = (0, 0);
        while p < end {
            let head = watches[p];
            watches[q] = head;
            p += 1;
            q += 1;
            match watch::occurrence(head) {
                Occurrence::Binary(other) => {
                    if other == not_repr {
                        continue;
                    }
                    let value = self.value(other);
                    if value < 0 {
                        break;
                    }
                    if value > 0 {
                        continue;
                    }
                    if other == repr {
                        self.proof_lits(ProofStep::Add, &[lit]);
                        self.assign(0, lit, Reason::Unit);
                        self.statistics.sweep_units += 1;
                        break;
                    }
                    self.proof_lits(ProofStep::Add, &[repr, other]);
                    self.proof_lits(ProofStep::Delete, &[lit, other]);
                    delayed.push(head);
                    self.substitute_watch(other, watch::binary(lit), watch::binary(repr));
                    q -= 1;
                }
                Occurrence::Large(at) => {
                    match self.substitute_large(lit, repr, head, at, &mut delayed) {
                        Step::Keep => {}
                        Step::Move => q -= 1,
                        Step::Stop => break,
                    }
                }
            }
        }
        watches.copy_within(p..end, q);
        watches.truncate(q + end - p);
        self.clauses.watches[widen(lit)] = watches;
        self.clauses.watches[widen(repr)].extend(delayed);
    }

    fn substitute_large(
        &mut self,
        lit: u32,
        repr: u32,
        head: u32,
        at: Ref,
        delayed: &mut Vec<u32>,
    ) -> Step {
        if self.clauses.arena.garbage(at) {
            return Step::Keep;
        }
        let not_repr = not(repr);
        let mut repr_watched = false;
        for position in 0..self.clauses.arena.size(at) {
            let other = self.clauses.arena.lit(at, position);
            if other == lit {
                self.clause.push(repr);
            } else if other == repr {
                repr_watched = true;
            } else if other == not_repr || self.value(other) > 0 {
                self.clause.clear();
                self.mark_clause_as_garbage(at);
                return Step::Keep;
            } else if self.value(other) == 0 {
                self.clause.push(other);
            }
        }
        match *self.clause.as_slice() {
            [] => {
                self.inconsistent = true;
                self.proof_lits(ProofStep::Add, &[]);
                return Step::Stop;
            }
            [unit] => {
                self.clause.clear();
                self.proof_lits(ProofStep::Add, &[unit]);
                self.assign(0, unit, Reason::Unit);
                self.statistics.sweep_units += 1;
                return Step::Stop;
            }
            _ => {}
        }
        self.proof_replace_clause(at);
        if !self.clauses.arena.redundant(at) {
            for position in 0..self.clause.len() {
                self.mark_added_literal(self.clause[position]);
            }
        }
        if let [first, second] = *self.clause.as_slice() {
            self.clause.clear();
            let other = first ^ second ^ repr;
            self.substitute_watch(other, watch::large(at), watch::binary(repr));
            self.statistics.clauses_irredundant -= 1;
            self.statistics.clauses_binary += 1;
            delayed.push(watch::binary(other));
            self.clauses.arena.set_garbage(at);
            return Step::Move;
        }
        let new_size = narrow(self.clause.len());
        for position in 0..new_size {
            self.clauses
                .arena
                .set_lit(at, position, self.clause[widen(position)]);
        }
        if new_size < self.clauses.arena.size(at) {
            self.clauses.arena.shrink(at, new_size);
            self.clauses.arena.set_searched(at, INITIAL_SEARCHED);
        }
        if !repr_watched {
            delayed.push(head);
        }
        self.clause.clear();
        Step::Move
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Step {
    Keep,
    Move,
    Stop,
}

impl Solver {
    fn sweep_equivalence_candidates(
        &mut self,
        sweeper: &mut Sweeper,
        lit: u32,
        other: u32,
    ) -> bool {
        let not_other = not(other);
        let not_lit = not(lit);
        let len = sweeper.partition.len();
        let third = len > 3 && sweeper.partition[len - 4] != INVALID_LIT;
        let satisfiable = sweeper.kitten.status() == Status::Satisfiable;
        if satisfiable && sweeper.kitten.flip_literal(lit) {
            if third {
                sweeper.partition[len - 3] = other;
                sweeper.partition[len - 2] = INVALID_LIT;
                sweeper.partition.truncate(len - 1);
            } else {
                sweeper.partition.truncate(len - 3);
            }
            return false;
        }
        if satisfiable && sweeper.kitten.flip_literal(other) {
            if third {
                sweeper.partition[len - 2] = INVALID_LIT;
                sweeper.partition.truncate(len - 1);
            } else {
                sweeper.partition.truncate(len - 3);
            }
            return false;
        }
        for (first, second, core) in [(not_lit, other, 0), (lit, not_other, 1)] {
            sweeper.kitten.assume(first);
            sweeper.kitten.assume(second);
            match Solver::sweep_solve(sweeper) {
                Status::Unsatisfiable => self.save_core(sweeper, core),
                Status::Satisfiable => {
                    self.sweep_refine(sweeper);
                    sweeper.core[0].clear();
                    return false;
                }
                Status::Unknown | Status::Core => {
                    sweeper.core[0].clear();
                    return false;
                }
            }
        }
        self.statistics.sweep_equivalences += 1;
        for (core, first, second) in [(0, lit, not_other), (1, not_lit, other)] {
            self.add_core(sweeper, core);
            self.new_binary_clause(first, second);
            self.clear_core(sweeper, core);
        }
        let (repr, replaced) = if lit < other {
            (lit, other)
        } else {
            (other, lit)
        };
        sweeper.reprs[widen(replaced)] = repr;
        sweeper.reprs[widen(not(replaced))] = not(repr);
        self.substitute_connected_clauses(replaced, repr);
        self.substitute_connected_clauses(not(replaced), not(repr));
        sweeper.remove(replaced);
        self.schedule_inner(sweeper, idx(repr));
        true
    }

    fn sweep_variable(&mut self, sweeper: &mut Sweeper, idx: u32) {
        if !self.active[widen(idx)] || sweeper.reprs[widen(literal(idx))] != literal(idx) {
            return;
        }
        self.sweep_environment(sweeper, idx);
        match Solver::sweep_solve(sweeper) {
            Status::Satisfiable => self.sweep_satisfiable(sweeper),
            Status::Unsatisfiable => self.save_add_clear_core(sweeper),
            Status::Unknown | Status::Core => {}
        }
        self.clear_sweeper(sweeper);
        if !self.inconsistent && self.assignment.propagate != self.assignment.trail.len() {
            let _ = self.dense_propagate();
        }
    }

    fn sweep_environment(&mut self, sweeper: &mut Sweeper, idx: u32) {
        sweeper.add_literal_to_environment(0, literal(idx));
        let (mut expand, mut next, mut depth) = (0, 1, 1);
        loop {
            if sweeper.encoded >= sweeper.clauses {
                return;
            }
            if expand == next {
                if depth >= sweeper.depth {
                    return;
                }
                next = sweeper.vars.len();
                if expand == next {
                    return;
                }
                depth += 1;
            }
            let idx = sweeper.vars[expand];
            for lit in [literal(idx), not(literal(idx))] {
                let mut position = 0;
                while let Some(&word) = self.clauses.watches[widen(lit)].get(position) {
                    position += 1;
                    match watch::occurrence(word) {
                        Occurrence::Binary(other) => self.sweep_binary(sweeper, depth, lit, other),
                        Occurrence::Large(at) => self.sweep_reference(sweeper, depth, at),
                    }
                    if sweeper.vars.len() >= widen(sweeper.variables) {
                        return;
                    }
                }
            }
            expand += 1;
        }
    }

    fn sweep_satisfiable(&mut self, sweeper: &mut Sweeper) {
        let rounds = self.option_u32(Opt::Sweepfliprounds);
        self.init_backbone_and_partition(sweeper);
        while !sweeper.backbone.is_empty() {
            if self.inconsistent || self.terminated() || sweeper.ticks_hit() {
                return;
            }
            sweeper.flip_backbone_literals(rounds);
            if self.terminated() || sweeper.ticks_hit() {
                return;
            }
            let Some(lit) = sweeper.backbone.pop() else {
                break;
            };
            if self.active[widen(idx(lit))] {
                let _ = self.sweep_backbone_candidate(sweeper, lit);
            }
        }
        while !sweeper.partition.is_empty() {
            if self.inconsistent || self.terminated() || sweeper.ticks_hit() {
                return;
            }
            sweeper.flip_partition_literals(rounds);
            if self.terminated() || sweeper.ticks_hit() {
                return;
            }
            let len = sweeper.partition.len();
            if len > 2 {
                let (lit, other) = (sweeper.partition[len - 3], sweeper.partition[len - 2]);
                let _ = self.sweep_equivalence_candidates(sweeper, lit, other);
            } else {
                sweeper.partition.clear();
            }
        }
    }

    fn scheduable_variable(&self, sweeper: &Sweeper, idx: u32) -> Option<usize> {
        let limit = widen(sweeper.clauses);
        let pos = self.clauses.watches[widen(literal(idx))].len();
        let neg = self.clauses.watches[widen(not(literal(idx)))].len();
        (pos != 0 && pos <= limit && neg != 0 && neg <= limit).then_some(pos + neg)
    }

    fn schedule_sweeping(&mut self, sweeper: &mut Sweeper) {
        for idx in std::mem::take(&mut self.sweeping.schedule) {
            if !self.active[widen(idx)] || sweeper.scheduled(idx) {
                continue;
            }
            if self.scheduable_variable(sweeper, idx).is_none() {
                self.flags[widen(idx)].clear(Flag::Sweep);
                continue;
            }
            self.schedule_inner(sweeper, idx);
        }
        let incomplete = self.sweeping.incomplete;
        let mut fresh = Vec::new();
        for idx in 0..self.vars {
            if !self.active[widen(idx)]
                || incomplete && !self.flags[widen(idx)].has(Flag::Sweep)
                || sweeper.scheduled(idx)
            {
                continue;
            }
            let Some(occ) = self.scheduable_variable(sweeper, idx) else {
                self.flags[widen(idx)].clear(Flag::Sweep);
                continue;
            };
            fresh.push((narrow(occ), idx));
        }
        fresh.sort_by_key(|&(rank, _)| rank);
        for (_, idx) in fresh {
            sweeper.schedule_outer(idx);
        }
        if self.incomplete_variables() == 0 {
            if self.sweeping.incomplete {
                self.statistics.sweep_completed += 1;
            }
            for idx in sweeper.scheduled_variables() {
                self.flags[widen(idx)].set(Flag::Sweep);
            }
            self.sweeping.incomplete = true;
        }
    }

    fn incomplete_variables(&self) -> usize {
        (0..self.vars)
            .filter(|&idx| self.active[widen(idx)] && self.flags[widen(idx)].has(Flag::Sweep))
            .count()
    }

    fn unschedule_sweeping(&mut self, sweeper: &Sweeper) {
        for idx in sweeper.scheduled_variables() {
            if self.active[widen(idx)] {
                self.sweeping.schedule.push(idx);
            }
        }
        if self.incomplete_variables() == 0 {
            self.sweeping.incomplete = false;
            self.statistics.sweep_completed += 1;
        }
    }

    pub(crate) fn sweep(&mut self) -> bool {
        if self.option(Opt::Sweep) == 0
            || self.inconsistent
            || self.terminated()
            || self.sweeping.delay.delaying()
        {
            return false;
        }
        let before = self.statistics.sweep_equivalences + self.statistics.sweep_units;
        let mut sweeper = self.init_sweeper();
        self.schedule_sweeping(&mut sweeper);
        let mut swept = 0_u64;
        while !self.inconsistent && !self.terminated() && sweeper.kitten.ticks() <= sweeper.ticks {
            let Some(idx) = sweeper.next_scheduled() else {
                break;
            };
            self.flags[widen(idx)].clear(Flag::Sweep);
            self.sweep_variable(&mut sweeper, idx);
            swept += 1;
        }
        self.unschedule_sweeping(&sweeper);
        self.release_sweeper(&sweeper);
        if !self.inconsistent {
            self.assignment.propagate = 0;
            let _ = self.propagate(Propagation::Probing);
        }
        let eliminated = self.statistics.sweep_equivalences + self.statistics.sweep_units - before;
        if average(real(eliminated), real(swept)) < MIN_AVERAGE {
            self.sweeping.delay.bump();
        } else {
            self.sweeping.delay.reduce();
        }
        eliminated > 0
    }
}
