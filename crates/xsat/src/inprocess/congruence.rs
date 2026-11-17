use std::{cmp::Ordering, collections::VecDeque};

use crate::{
    inprocess::{backbone::Watching, dense::Rewatch},
    options::Opt,
    solver::{idx, negated, not, Flush, Propagation, Solver, TRUE},
    store::{
        arena::{Ref, INVALID_LIT},
        convert::{narrow, real, widen},
        watch::{self, Head},
    },
    trace::proof::Step as ProofStep,
};

const SIZE_NONCES: usize = 16;
const NONCE_SHIFT: u32 = 4;
const HALF: u32 = 32;
const MAX_ARITY: u32 = (1 << 26) - 1;
const MATCHED: i8 = 2;
const KEPT: i8 = 4;
const BASE: i8 = 1;
const MIN_EQUIVALENT_RATE: f64 = 0.001;
const SMALLEST_GATE_CLAUSE: u32 = 3;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Tag {
    And,
    Xor,
    Ite,
}

impl Tag {
    const fn nonce(self) -> usize {
        match self {
            Tag::And => 0,
            Tag::Xor => 1,
            Tag::Ite => 2,
        }
    }
}

#[derive(Clone, Debug)]
struct Gate {
    lhs: u32,
    hash: u32,
    tag: Tag,
    garbage: bool,
    indexed: bool,
    rhs: Vec<u32>,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Found {
    Nothing,
    Falsifying(u32),
    Clashing(u32),
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Slot {
    Empty,
    Removed,
    Full(usize),
}

#[derive(Debug)]
struct Closure {
    scheduled: Vec<bool>,
    occurrences: Vec<Vec<usize>>,
    gates: Vec<Gate>,
    lits: Vec<u32>,
    binaries: Vec<[u32; 2]>,
    schedule: VecDeque<u32>,
    repr: Vec<u32>,
    table: Vec<Slot>,
    entries: usize,
    nonces: [u64; SIZE_NONCES],
    units: usize,
    negbincount: Vec<u32>,
    largecount: Vec<u32>,
    chain: Vec<u32>,
}

impl Closure {
    fn find_repr(&self, lit: u32) -> u32 {
        let mut res = lit;
        let mut next = self.repr[widen(res)];
        while res != next {
            res = next;
            next = self.repr[widen(res)];
        }
        res
    }

    fn hash_lits(&self, tag: Tag, lits: &[u32]) -> u32 {
        let mut n = tag.nonce();
        let mut hash: u64 = 0;
        for &lit in lits {
            hash = hash.wrapping_add(u64::from(lit));
            hash = hash.wrapping_mul(self.nonces[n]);
            n += 1;
            hash = hash.rotate_left(NONCE_SHIFT);
            if n == SIZE_NONCES {
                n = 0;
            }
        }
        hash ^= hash >> HALF;
        u32::try_from(hash & u64::from(u32::MAX)).unwrap_or(0)
    }

    fn reduce_hash(&self, hash: u32) -> usize {
        widen(hash) & (self.table.len() - 1)
    }

    fn resize(&mut self) {
        let new_size = if self.table.is_empty() {
            1
        } else {
            2 * self.table.len()
        };
        let old = std::mem::replace(&mut self.table, vec![Slot::Empty; new_size]);
        let mut flushed = 0;
        for slot in old {
            match slot {
                Slot::Empty => {}
                Slot::Removed => flushed += 1,
                Slot::Full(g) => {
                    let mut pos = self.reduce_hash(self.gates[g].hash);
                    while self.table[pos] != Slot::Empty {
                        pos = (pos + 1) % new_size;
                    }
                    self.table[pos] = Slot::Full(g);
                }
            }
        }
        self.entries -= flushed;
    }

    fn index_gate(&mut self, g: usize) {
        if 2 * self.entries >= self.table.len() {
            self.resize();
        }
        let mut pos = self.reduce_hash(self.gates[g].hash);
        while let Slot::Full(_) = self.table[pos] {
            pos = (pos + 1) % self.table.len();
        }
        self.table[pos] = Slot::Full(g);
        self.entries += 1;
        self.gates[g].indexed = true;
    }

    fn remove_gate(&mut self, g: usize) {
        if !self.gates[g].indexed {
            return;
        }
        let mut pos = self.reduce_hash(self.gates[g].hash);
        while self.table[pos] != Slot::Full(g) {
            pos = (pos + 1) % self.table.len();
        }
        self.table[pos] = Slot::Removed;
        self.gates[g].indexed = false;
    }

    fn find_gate(
        &mut self,
        tag: Tag,
        hash: u32,
        lits: &[u32],
        except: Option<usize>,
    ) -> Option<usize> {
        if self.entries == 0 {
            return None;
        }
        let start = self.reduce_hash(hash);
        let mut pos = start;
        while let slot @ (Slot::Removed | Slot::Full(_)) = self.table[pos] {
            if let Slot::Full(g) = slot {
                let gate = &self.gates[g];
                if gate.garbage {
                    self.gates[g].indexed = false;
                    self.table[pos] = Slot::Removed;
                } else if Some(g) != except
                    && gate.tag == tag
                    && gate.hash == hash
                    && gate.rhs == lits
                {
                    return Some(g);
                }
            }
            pos = (pos + 1) % self.table.len();
            if pos == start {
                break;
            }
        }
        None
    }

    fn find_lits(&mut self, tag: Tag, lits: &[u32], except: Option<usize>) -> (Option<usize>, u32) {
        let hash = self.hash_lits(tag, lits);
        (self.find_gate(tag, hash, lits, except), hash)
    }

    fn find_matching(&mut self, g: usize) -> (Option<usize>, u32, bool) {
        let mut rhs = std::mem::take(&mut self.gates[g].rhs);
        let tag = self.gates[g].tag;
        let negate = match tag {
            Tag::And | Tag::Xor => {
                rhs.sort_unstable();
                false
            }
            Tag::Ite => normalize_ite_lits(&mut rhs),
        };
        let (found, hash) = self.find_lits(tag, &rhs, Some(g));
        self.gates[g].rhs = rhs;
        (found, hash, negate)
    }

    fn new_gate(&mut self, tag: Tag, hash: u32, lhs: u32, rhs: Vec<u32>) -> usize {
        let g = self.gates.len();
        for &lit in &rhs {
            self.occurrences[widen(lit)].push(g);
        }
        self.gates.push(Gate {
            lhs,
            hash,
            tag,
            garbage: false,
            indexed: false,
            rhs,
        });
        self.index_gate(g);
        g
    }

    fn reindex(&mut self, g: usize, hash: u32) {
        self.remove_gate(g);
        self.gates[g].hash = hash;
        self.index_gate(g);
    }

    fn schedule_literal(&mut self, lit: u32) {
        let scheduled = &mut self.scheduled[widen(idx(lit))];
        if !*scheduled {
            *scheduled = true;
            self.schedule.push_back(lit);
        }
    }
}

fn normalize_ite_lits(lits: &mut [u32]) -> bool {
    if negated(lits[0]) {
        lits[0] = not(lits[0]);
        lits.swap(1, 2);
    }
    if !negated(lits[1]) {
        return false;
    }
    lits[1] = not(lits[1]);
    lits[2] = not(lits[2]);
    true
}

fn inc_lits(lits: &mut [u32]) {
    for lit in lits {
        *lit = not(*lit);
        if negated(*lit) {
            break;
        }
    }
}

fn parity_lits(lits: &[u32]) -> u32 {
    lits.iter().fold(0, |parity, &lit| parity ^ (lit & 1))
}

fn sort_pairs(pairs: &mut [[u32; 2]]) {
    pairs.sort_by_key(|pair| (pair[0], pair[1]));
}

fn leading_binaries(watches: &[u32]) -> impl Iterator<Item = u32> + '_ {
    watches.iter().map_while(|&word| match watch::decode(word) {
        Head::Binary(other) => Some(other),
        Head::Blocking(_) => None,
    })
}

fn large_occurrences(watches: &[u32]) -> impl Iterator<Item = Ref> + '_ {
    watches
        .iter()
        .take_while(|&&word| matches!(watch::decode(word), Head::Blocking(_)))
        .map(|&word| watch::large_ref(word))
}

fn search_condeq(
    pos_lit: u32,
    pos: &[[u32; 2]],
    neg_lit: u32,
    neg: &[[u32; 2]],
    condeq: &mut Vec<[u32; 2]>,
) {
    for pair in pos {
        let other = pair[1];
        let not_other = not(other);
        if neg
            .binary_search_by_key(&not_other, |pair| pair[1])
            .is_err()
        {
            continue;
        }
        let (first, second) = if negated(pos_lit) {
            (neg_lit, other)
        } else {
            (pos_lit, not_other)
        };
        condeq.push([first, second]);
        if negated(second) {
            condeq.push([not(second), not(first)]);
        } else {
            condeq.push([second, first]);
        }
    }
}

fn extract_condeq_pairs(condbin: &[[u32; 2]], condeq: &mut Vec<[u32; 2]>) {
    let end = condbin.len();
    let skip_negative = |mut at: usize| {
        while at < end && negated(condbin[at][0]) {
            at += 1;
        }
        at
    };
    let mut pos_begin = skip_negative(0);
    while pos_begin < end {
        let pos_lit = condbin[pos_begin][0];
        let mut pos_end = pos_begin + 1;
        while pos_end < end && condbin[pos_end][0] == pos_lit {
            pos_end += 1;
        }
        if pos_end == end {
            return;
        }
        let next_lit = condbin[pos_end][0];
        let neg_lit = not(pos_lit);
        if next_lit != neg_lit {
            pos_begin = if negated(next_lit) {
                skip_negative(pos_end + 1)
            } else {
                pos_end
            };
            continue;
        }
        let neg_begin = pos_end;
        let mut neg_end = neg_begin + 1;
        while neg_end < end && condbin[neg_end][0] == neg_lit {
            neg_end += 1;
        }
        let pos = &condbin[pos_begin..pos_end];
        let neg = &condbin[neg_begin..neg_end];
        if pos.len() <= neg.len() {
            search_condeq(pos_lit, pos, neg_lit, neg, condeq);
        } else {
            search_condeq(neg_lit, neg, pos_lit, pos, condeq);
        }
        if neg_end == end {
            return;
        }
        pos_begin = if negated(condbin[neg_end][0]) {
            skip_negative(neg_end + 1)
        } else {
            neg_end
        };
    }
}

impl Solver {
    fn learn_congruence_unit(&mut self, unit: u32) -> bool {
        let value = self.value(unit);
        if value > 0 {
            return true;
        }
        if value < 0 {
            self.inconsistent = true;
            self.proof_lits(ProofStep::Add, &[]);
            return false;
        }
        self.learned_unit(unit);
        self.propagate_trail(Propagation::Probing, None, Flush::Keep)
            .is_none()
    }

    fn add_congruence_binary(&mut self, closure: &mut Closure, a: u32, b: u32) {
        if self.inconsistent || a == not(b) {
            return;
        }
        let a_value = self.value(a);
        if a_value > 0 {
            return;
        }
        let b_value = self.value(b);
        if b_value > 0 {
            return;
        }
        let unit = if a == b {
            Some(a)
        } else if a_value < 0 && b_value == 0 {
            Some(b)
        } else if a_value == 0 && b_value < 0 {
            Some(a)
        } else {
            None
        };
        if let Some(unit) = unit {
            let _ = self.learn_congruence_unit(unit);
        } else if self.clauses.watching == Watching::Dense {
            self.new_unwatched_binary_clause(a, b);
            closure.binaries.push([a.min(b), a.max(b)]);
        } else {
            self.new_binary_clause(a, b);
        }
    }

    fn merge_literals(&mut self, closure: &mut Closure, lit: u32, other: u32) -> bool {
        let repr_lit = closure.find_repr(lit);
        let repr_other = closure.find_repr(other);
        if repr_lit == repr_other {
            return false;
        }
        let lit_value = self.value(lit);
        let other_value = self.value(other);
        if lit_value != 0 {
            if lit_value == other_value {
                return false;
            }
            if lit_value == -other_value {
                self.inconsistent = true;
                self.proof_lits(ProofStep::Add, &[]);
                return false;
            }
            let _ = self.learn_congruence_unit(if lit_value < 0 { not(other) } else { other });
            return false;
        }
        if other_value != 0 {
            let _ = self.learn_congruence_unit(if other_value < 0 { not(lit) } else { lit });
            return false;
        }
        let smaller = repr_lit.min(repr_other);
        let larger = repr_lit.max(repr_other);
        if repr_lit == not(repr_other) {
            self.learned_unit(smaller);
            self.inconsistent = true;
            self.proof_lits(ProofStep::Add, &[]);
            return false;
        }
        closure.repr[widen(larger)] = smaller;
        closure.repr[widen(not(larger))] = not(smaller);
        self.add_congruence_binary(closure, not(larger), smaller);
        self.add_congruence_binary(closure, larger, not(smaller));
        closure.schedule_literal(larger);
        true
    }

    fn mark_gate_as_garbage(closure: &mut Closure, g: usize) {
        closure.gates[g].garbage = true;
    }

    fn match_or_index(
        &mut self,
        closure: &mut Closure,
        g: usize,
        found: Option<usize>,
        hash: u32,
        chain: Chain,
    ) -> bool {
        if let Some(h) = found {
            let (g_lhs, h_lhs) = (closure.gates[g].lhs, closure.gates[h].lhs);
            match chain {
                Chain::None => {}
                Chain::Xor => self.add_xor_matching_proof_chain(closure, g, g_lhs, h_lhs),
                Chain::TurnedIte => self.add_ite_turned_and_binary_clauses(closure, g),
            }
            let _ = self.merge_literals(closure, g_lhs, h_lhs);
            if chain != Chain::None && !self.inconsistent {
                self.delete_proof_chain(closure);
            }
            true
        } else {
            closure.reindex(g, hash);
            false
        }
    }

    fn new_and_gate(&mut self, closure: &mut Closure, lhs: u32) {
        let mut rhs: Vec<u32> = closure
            .lits
            .iter()
            .filter(|&&lit| lit != lhs)
            .map(|&lit| not(lit))
            .collect();
        rhs.sort_unstable();
        let (found, hash) = closure.find_lits(Tag::And, &rhs, None);
        if let Some(g) = found {
            let g_lhs = closure.gates[g].lhs;
            let _ = self.merge_literals(closure, g_lhs, lhs);
            return;
        }
        let _ = closure.new_gate(Tag::And, hash, lhs, rhs);
    }

    fn new_xor_gate(&mut self, closure: &mut Closure, lhs: u32) -> bool {
        let not_lhs = not(lhs);
        let mut rhs: Vec<u32> = closure
            .lits
            .iter()
            .copied()
            .filter(|&lit| lit != lhs && lit != not_lhs)
            .collect();
        rhs.sort_unstable();
        let (found, hash) = closure.find_lits(Tag::Xor, &rhs, None);
        if let Some(g) = found {
            let g_lhs = closure.gates[g].lhs;
            let _ = self.merge_literals(closure, g_lhs, lhs);
            return false;
        }
        let _ = closure.new_gate(Tag::Xor, hash, lhs, rhs);
        true
    }

    fn new_ite_gate(
        &mut self,
        closure: &mut Closure,
        lhs: u32,
        cond: u32,
        then_lit: u32,
        else_lit: u32,
    ) {
        if else_lit == not(then_lit) {
            return;
        }
        if else_lit == then_lit {
            let _ = self.merge_literals(closure, lhs, then_lit);
            return;
        }
        let mut rhs = vec![cond, then_lit, else_lit];
        let negate = normalize_ite_lits(&mut rhs);
        let lhs = if negate { not(lhs) } else { lhs };
        let (found, hash) = closure.find_lits(Tag::Ite, &rhs, None);
        if let Some(g) = found {
            let g_lhs = closure.gates[g].lhs;
            self.add_ite_matching_proof_chain(closure, g, g_lhs, lhs);
            let _ = self.merge_literals(closure, g_lhs, lhs);
            if !self.inconsistent {
                self.delete_proof_chain(closure);
            }
            return;
        }
        let _ = closure.new_gate(Tag::Ite, hash, lhs, rhs);
    }

    fn update_and_gate(&mut self, closure: &mut Closure, g: usize, rhs: Vec<u32>, found: Found) {
        let lhs = closure.gates[g].lhs;
        closure.gates[g].rhs = match found {
            Found::Falsifying(lit) => vec![lit],
            Found::Clashing(lit) => vec![lit, not(lit)],
            Found::Nothing => rhs,
        };
        let garbage = if found != Found::Nothing {
            let _ = self.learn_congruence_unit(not(lhs));
            true
        } else if closure.gates[g].rhs.len() == 1 {
            self.update_unary_gate(closure, g);
            true
        } else {
            let (found, hash, _) = closure.find_matching(g);
            self.match_or_index(closure, g, found, hash, Chain::None)
        };
        if garbage && !self.inconsistent {
            Solver::mark_gate_as_garbage(closure, g);
        }
    }

    fn update_unary_gate(&mut self, closure: &mut Closure, g: usize) {
        let (lhs, rhs) = (closure.gates[g].lhs, closure.gates[g].rhs[0]);
        match self.value(lhs).cmp(&0) {
            Ordering::Greater => {
                let _ = self.learn_congruence_unit(rhs);
            }
            Ordering::Less => {
                let _ = self.learn_congruence_unit(not(rhs));
            }
            Ordering::Equal => {
                let _ = self.merge_literals(closure, lhs, rhs);
            }
        }
    }

    fn skip_and_gate(&self, closure: &mut Closure, g: usize) -> bool {
        if closure.gates[g].garbage {
            return true;
        }
        if self.value(closure.gates[g].lhs) > 0 {
            Solver::mark_gate_as_garbage(closure, g);
            return true;
        }
        false
    }

    fn simplify_and_gate(&mut self, closure: &mut Closure, g: usize) {
        if self.skip_and_gate(closure, g) {
            return;
        }
        let mut found = Found::Nothing;
        let mut rhs = Vec::new();
        for &lit in &closure.gates[g].rhs {
            let value = self.value(lit);
            if value > 0 {
                continue;
            }
            if value < 0 {
                found = Found::Falsifying(lit);
                continue;
            }
            rhs.push(lit);
        }
        self.update_and_gate(closure, g, rhs, found);
    }

    fn rewrite_and_gate(&mut self, closure: &mut Closure, g: usize, dst: u32, src: u32) {
        if self.skip_and_gate(closure, g) || !closure.gates[g].rhs.contains(&src) {
            return;
        }
        let not_lhs = not(closure.gates[g].lhs);
        let not_dst = not(dst);
        let mut found = Found::Nothing;
        let mut dst_count = 0;
        let mut not_dst_count = 0;
        let mut rhs = Vec::new();
        for &old in &closure.gates[g].rhs {
            let lit = if old == src { dst } else { old };
            if lit == not_lhs {
                found = Found::Clashing(lit);
                break;
            }
            let value = self.value(lit);
            if value > 0 {
                continue;
            }
            if value < 0 {
                found = Found::Falsifying(lit);
                break;
            }
            if lit == dst {
                if not_dst_count > 0 {
                    found = Found::Clashing(not_dst);
                    break;
                }
                dst_count += 1;
                if dst_count > 1 {
                    continue;
                }
            }
            if lit == not_dst {
                if dst_count > 0 {
                    found = Found::Clashing(dst);
                    break;
                }
                not_dst_count += 1;
            }
            rhs.push(lit);
        }
        self.update_and_gate(closure, g, rhs, found);
    }

    fn update_xor_gate(&mut self, closure: &mut Closure, g: usize) {
        let garbage = match closure.gates[g].rhs.len() {
            0 => {
                let lhs = closure.gates[g].lhs;
                let _ = self.learn_congruence_unit(not(lhs));
                true
            }
            1 => {
                self.update_unary_gate(closure, g);
                true
            }
            _ => {
                let (found, hash, _) = closure.find_matching(g);
                self.match_or_index(closure, g, found, hash, Chain::Xor)
            }
        };
        if garbage && !self.inconsistent {
            Solver::mark_gate_as_garbage(closure, g);
        }
    }

    fn simplify_xor_gate(&mut self, closure: &mut Closure, g: usize) {
        if closure.gates[g].garbage {
            return;
        }
        let mut negate = false;
        let mut rhs = Vec::new();
        for &lit in &closure.gates[g].rhs {
            let value = self.value(lit);
            if value > 0 {
                negate = !negate;
            }
            if value == 0 {
                rhs.push(lit);
            }
        }
        let gate = &mut closure.gates[g];
        if negate {
            gate.lhs = not(gate.lhs);
        }
        gate.rhs = rhs;
        self.update_xor_gate(closure, g);
    }

    fn rewrite_xor_gate(&mut self, closure: &mut Closure, g: usize, dst: u32, src: u32) {
        let gate = &closure.gates[g];
        if gate.garbage {
            return;
        }
        if dst == gate.lhs || dst == not(gate.lhs) {
            Solver::mark_gate_as_garbage(closure, g);
            return;
        }
        if !gate.rhs.contains(&src) {
            return;
        }
        let dst_negated = negated(dst);
        let mut negate = dst_negated;
        let dst = dst & !1;
        let mut dst_count = 0;
        let mut rhs = Vec::new();
        for &old in &gate.rhs {
            let lit = if old == src { dst } else { old };
            let value = self.value(lit);
            if value > 0 {
                negate = !negate;
            }
            if value != 0 {
                continue;
            }
            if lit == dst {
                dst_count += 1;
            }
            rhs.push(lit);
        }
        if dst_count == 2 {
            rhs.retain(|&lit| lit != dst);
        }
        let gate = &mut closure.gates[g];
        if negate {
            gate.lhs = not(gate.lhs);
        }
        gate.rhs = rhs;
        if dst_count > 1 && self.proof.is_some() {
            let lhs = closure.gates[g].lhs;
            let rhs = closure.gates[g].rhs.clone();
            self.add_xor_shrinking_proof_chain(&rhs, lhs, src);
        }
        self.update_xor_gate(closure, g);
        if !closure.gates[g].garbage && !self.inconsistent && dst_negated && dst_count == 1 {
            closure.occurrences[widen(dst)].push(g);
        }
    }

    fn turn_ite_gate(
        &mut self,
        closure: &mut Closure,
        g: usize,
        tag: Tag,
        mut rhs: [u32; 2],
        old: [u32; 3],
        dst: Option<u32>,
    ) -> bool {
        if rhs[0] > rhs[1] {
            rhs.swap(0, 1);
        }
        if tag == Tag::Xor {
            let mut negate = false;
            for lit in &mut rhs {
                if negated(*lit) {
                    *lit = not(*lit);
                    negate = !negate;
                }
            }
            if negate {
                closure.gates[g].lhs = not(closure.gates[g].lhs);
            }
        }
        closure.gates[g].tag = tag;
        closure.gates[g].rhs = rhs.to_vec();
        let (found, hash, _) = closure.find_matching(g);
        let chain = match tag {
            Tag::Xor => Chain::Xor,
            Tag::And | Tag::Ite => Chain::TurnedIte,
        };
        if self.match_or_index(closure, g, found, hash, chain) {
            return true;
        }
        for lit in closure.gates[g].rhs.clone() {
            if Some(lit) != dst && !old.contains(&lit) {
                closure.occurrences[widen(lit)].push(g);
            }
        }
        if dst.is_some() && tag == Tag::And {
            let not_lhs = not(closure.gates[g].lhs);
            for lit in closure.gates[g].rhs.clone() {
                self.add_congruence_binary(closure, not_lhs, lit);
            }
        }
        false
    }

    fn simplify_ite_gate(&mut self, closure: &mut Closure, g: usize) {
        if closure.gates[g].garbage {
            return;
        }
        let lhs = closure.gates[g].lhs;
        let old = [
            closure.gates[g].rhs[0],
            closure.gates[g].rhs[1],
            closure.gates[g].rhs[2],
        ];
        let [cond, then_lit, else_lit] = old;
        let selected = match self.value(cond).cmp(&0) {
            Ordering::Greater => Some(then_lit),
            Ordering::Less => Some(else_lit),
            Ordering::Equal => None,
        };
        let mut garbage = true;
        if let Some(selected) = selected {
            let _ = self.merge_literals(closure, lhs, selected);
        } else {
            let then_value = self.value(then_lit);
            let else_value = self.value(else_lit);
            let not_lhs = not(lhs);
            if then_value > 0 && else_value > 0 {
                let _ = self.learn_congruence_unit(lhs);
            } else if then_value < 0 && else_value < 0 {
                let _ = self.learn_congruence_unit(not_lhs);
            } else if then_value > 0 && else_value < 0 {
                let _ = self.merge_literals(closure, lhs, cond);
            } else if then_value < 0 && else_value > 0 {
                let _ = self.merge_literals(closure, lhs, not(cond));
            } else {
                let rhs = if then_value > 0 {
                    closure.gates[g].lhs = not_lhs;
                    [not(cond), not(else_lit)]
                } else if then_value < 0 {
                    [not(cond), else_lit]
                } else if else_value > 0 {
                    closure.gates[g].lhs = not_lhs;
                    [not(then_lit), cond]
                } else {
                    [cond, then_lit]
                };
                garbage = self.turn_ite_gate(closure, g, Tag::And, rhs, old, None);
            }
        }
        if garbage && !self.inconsistent {
            Solver::mark_gate_as_garbage(closure, g);
        }
    }

    fn rewrite_ite_gate(&mut self, closure: &mut Closure, g: usize, dst: u32, src: u32) {
        if closure.gates[g].garbage || !closure.gates[g].rhs.contains(&src) {
            return;
        }
        let lhs = closure.gates[g].lhs;
        let old = [
            closure.gates[g].rhs[0],
            closure.gates[g].rhs[1],
            closure.gates[g].rhs[2],
        ];
        let [cond, then_lit, else_lit] = old;
        let not_lhs = not(lhs);
        let not_dst = not(dst);
        let mut tag = Tag::And;
        let mut rhs = old;
        let mut garbage = false;
        let mut shrink = true;
        if src == cond {
            if dst == then_lit || not_dst == else_lit {
                closure.gates[g].lhs = not_lhs;
                rhs[0] = not(then_lit);
                rhs[1] = not(else_lit);
            } else if not_dst == then_lit || dst == else_lit {
                rhs[0] = else_lit;
            } else {
                shrink = false;
                rhs[0] = dst;
            }
        } else if src == then_lit {
            if dst == cond {
                closure.gates[g].lhs = not_lhs;
                rhs[0] = not(cond);
                rhs[1] = not(else_lit);
            } else if not_dst == cond {
                rhs[0] = not(cond);
                rhs[1] = else_lit;
            } else if dst == else_lit {
                let _ = self.merge_literals(closure, lhs, else_lit);
                garbage = true;
            } else if not_dst == else_lit {
                tag = Tag::Xor;
                rhs[1] = else_lit;
            } else {
                shrink = false;
                rhs[1] = dst;
            }
        } else if dst == cond {
        } else if not_dst == cond {
            closure.gates[g].lhs = not_lhs;
            rhs[1] = not(then_lit);
        } else if dst == then_lit {
            let _ = self.merge_literals(closure, lhs, then_lit);
            garbage = true;
        } else if not_dst == then_lit {
            tag = Tag::Xor;
            closure.gates[g].lhs = not_lhs;
        } else {
            shrink = false;
            rhs[2] = dst;
        }
        if !garbage {
            if shrink {
                garbage = self.turn_ite_gate(closure, g, tag, [rhs[0], rhs[1]], old, Some(dst));
            } else {
                closure.gates[g].rhs = rhs.to_vec();
                let (found, hash, negate) = closure.find_matching(g);
                if let Some(h) = found {
                    garbage = true;
                    let normalized = if negate { not_lhs } else { lhs };
                    let h_lhs = closure.gates[h].lhs;
                    self.add_ite_matching_proof_chain(closure, h, h_lhs, normalized);
                    let _ = self.merge_literals(closure, h_lhs, normalized);
                    if !self.inconsistent {
                        self.delete_proof_chain(closure);
                    }
                } else {
                    closure.remove_gate(g);
                    if negate {
                        closure.gates[g].lhs = not_lhs;
                    }
                    closure.gates[g].hash = hash;
                    closure.index_gate(g);
                    for lit in closure.gates[g].rhs.clone() {
                        if lit != dst && !old.contains(&lit) {
                            closure.occurrences[widen(lit)].push(g);
                        }
                    }
                }
            }
        }
        if garbage && !self.inconsistent {
            Solver::mark_gate_as_garbage(closure, g);
        }
    }

    fn simplify_gate(&mut self, closure: &mut Closure, g: usize) -> bool {
        match closure.gates[g].tag {
            Tag::And => self.simplify_and_gate(closure, g),
            Tag::Xor => self.simplify_xor_gate(closure, g),
            Tag::Ite => self.simplify_ite_gate(closure, g),
        }
        !self.inconsistent
    }

    fn rewrite_gate(&mut self, closure: &mut Closure, g: usize, dst: u32, src: u32) -> bool {
        match closure.gates[g].tag {
            Tag::And => self.rewrite_and_gate(closure, g, dst, src),
            Tag::Xor => self.rewrite_xor_gate(closure, g, dst, src),
            Tag::Ite => self.rewrite_ite_gate(closure, g, dst, src),
        }
        !self.inconsistent
    }

    fn extract_binaries(&mut self, closure: &mut Closure) {
        if self.option(Opt::Congruencebinaries) == 0 {
            return;
        }
        let mut ranges = vec![(0, 0); widen(2 * self.vars)];
        let mut start = 0;
        while start < closure.binaries.len() {
            let lit = closure.binaries[start][0];
            let mut end = start + 1;
            while end < closure.binaries.len() && closure.binaries[end][0] == lit {
                end += 1;
            }
            closure.binaries[start..end].sort_by_key(|pair| pair[1]);
            ranges[widen(lit)] = (start, end);
            start = end;
        }
        let before = closure.binaries.len();
        let original = closure.binaries[..before].to_vec();
        let find = |lit: u32, other: u32| {
            let (lit, other) = (lit.min(other), lit.max(other));
            let (start, end) = ranges[widen(lit)];
            original[start..end]
                .binary_search_by_key(&other, |pair| pair[1])
                .is_ok()
        };
        for ternary in self.irredundant_clauses() {
            if self.clauses.arena.size(ternary) != SMALLEST_GATE_CLAUSE {
                continue;
            }
            let [x, y, z] = [
                self.clauses.arena.lit(ternary, 0),
                self.clauses.arena.lit(ternary, 1),
                self.clauses.arena.lit(ternary, 2),
            ];
            if self.value(x) != 0 || self.value(y) != 0 || self.value(z) != 0 {
                continue;
            }
            let (first, second) = if find(not(x), y) || find(not(x), z) {
                (y, z)
            } else if find(not(y), x) || find(not(y), z) {
                (x, z)
            } else if find(not(z), x) || find(not(z), y) {
                (x, y)
            } else {
                continue;
            };
            if !find(first, second) {
                self.add_congruence_binary(closure, first, second);
            }
        }
        closure.binaries[before..].sort_by_key(|pair| (pair[0], pair[1]));
        let mut kept = before;
        for position in before..closure.binaries.len() {
            let pair = closure.binaries[position];
            if position == before || pair != closure.binaries[kept - 1] {
                closure.binaries[kept] = pair;
                kept += 1;
            } else {
                self.delete_binary(pair[0], pair[1]);
            }
        }
        closure.binaries.truncate(kept);
    }

    fn irredundant_clauses(&self) -> Vec<Ref> {
        self.clauses
            .arena
            .refs()
            .take_while(|&at| self.clauses.last_irredundant.is_none_or(|last| at <= last))
            .filter(|&at| !self.clauses.arena.garbage(at) && !self.clauses.arena.redundant(at))
            .collect()
    }

    fn find_first_and_gate(&mut self, closure: &mut Closure, lhs: u32, marked: &mut Vec<u32>) {
        let not_lhs = not(lhs);
        let arity = closure.lits.len() - 1;
        let mut matched = 0;
        for other in watch::binaries(&self.clauses.watches[widen(not_lhs)]) {
            if self.marks[widen(other)] != 0 {
                matched += 1;
                self.marks[widen(other)] |= MATCHED;
                marked.push(other);
            }
        }
        if matched >= arity {
            self.new_and_gate(closure, lhs);
        }
    }

    fn find_remaining_and_gate(&mut self, closure: &mut Closure, lhs: u32, marked: &mut Vec<u32>) {
        let not_lhs = not(lhs);
        if self.marks[widen(not_lhs)] < MATCHED {
            return;
        }
        let arity = closure.lits.len() - 1;
        let mut matched = 0;
        for other in watch::binaries(&self.clauses.watches[widen(not_lhs)]) {
            let mark = self.marks[widen(other)];
            if mark == 0 {
                continue;
            }
            matched += 1;
            if mark & MATCHED != 0 {
                self.marks[widen(other)] = mark | KEPT;
            }
        }
        let marks = &mut self.marks;
        marked.retain(|&lit| {
            let keep = lit != not_lhs && marks[widen(lit)] & KEPT != 0;
            marks[widen(lit)] = if keep { BASE | MATCHED } else { BASE };
            keep
        });
        if matched >= arity {
            self.new_and_gate(closure, lhs);
        }
    }

    fn extract_and_gates_with_base_clause(&mut self, closure: &mut Closure, c: Ref) {
        let arity_limit = self.option_u32(Opt::Congruenceandarity).min(MAX_ARITY);
        let size_limit = arity_limit + 1;
        closure.lits.clear();
        let mut size = 0;
        let mut max_negbincount = 0;
        for position in 0..self.clauses.arena.size(c) {
            let lit = self.clauses.arena.lit(c, position);
            let value = self.value(lit);
            if value < 0 {
                continue;
            }
            if value > 0 {
                self.mark_clause_as_garbage(c);
                return;
            }
            size += 1;
            if size > size_limit {
                return;
            }
            let count = closure.negbincount[widen(lit)];
            if count == 0 {
                return;
            }
            max_negbincount = max_negbincount.max(count);
            closure.lits.push(lit);
        }
        if size < SMALLEST_GATE_CLAUSE {
            return;
        }
        let arity = size - 1;
        if max_negbincount < arity {
            return;
        }
        let mut reduced = 0;
        for p in 0..closure.lits.len() {
            let lit = closure.lits[p];
            self.marks[widen(not(lit))] = BASE;
            if closure.negbincount[widen(lit)] < arity {
                if reduced < p {
                    closure.lits[p] = closure.lits[reduced];
                    closure.lits[reduced] = lit;
                    reduced += 1;
                } else if reduced == p {
                    reduced += 1;
                }
            }
        }
        let negbincount = &closure.negbincount;
        closure.lits[reduced..].sort_by_key(|&lit| (negbincount[widen(lit)], lit));
        let candidates = closure.lits[reduced..].to_vec();
        let mut marked = Vec::new();
        for (position, lhs) in candidates.into_iter().enumerate() {
            if self.inconsistent || self.clauses.arena.garbage(c) {
                break;
            }
            if position == 0 {
                self.find_first_and_gate(closure, lhs, &mut marked);
            } else if marked.is_empty() {
                break;
            } else {
                self.find_remaining_and_gate(closure, lhs, &mut marked);
            }
        }
        for position in 0..closure.lits.len() {
            self.marks[widen(not(closure.lits[position]))] = 0;
        }
    }

    fn extract_and_gates(&mut self, closure: &mut Closure) {
        if self.option(Opt::Congruenceands) == 0 {
            return;
        }
        let mut negbincount = vec![0; widen(2 * self.vars)];
        for &[lit, other] in &closure.binaries {
            negbincount[widen(not(lit))] += 1;
            negbincount[widen(not(other))] += 1;
            self.watch_binary(lit, other);
        }
        closure.negbincount = negbincount;
        for c in self.irredundant_clauses() {
            if self.terminated() || self.inconsistent {
                break;
            }
            if self.clauses.arena.garbage(c) {
                continue;
            }
            self.extract_and_gates_with_base_clause(closure, c);
        }
        for watches in &mut self.clauses.watches {
            watches.clear();
        }
    }

    fn find_large_xor_side_clause(&mut self, closure: &Closure) -> bool {
        let mut least = None;
        let mut least_count = u32::MAX;
        for &lit in &closure.lits {
            self.marks[widen(lit)] = TRUE;
            let count = closure.largecount[widen(lit)];
            if count < least_count {
                least_count = count;
                least = Some(lit);
            }
        }
        let mut found = false;
        if let Some(least) = least {
            let occurrences: Vec<Ref> =
                large_occurrences(&self.clauses.watches[widen(least)]).collect();
            for c in occurrences {
                if self.clauses.arena.garbage(c)
                    || widen(self.clauses.arena.size(c)) < closure.lits.len()
                {
                    continue;
                }
                let mut subset = true;
                for position in 0..self.clauses.arena.size(c) {
                    let other = self.clauses.arena.lit(c, position);
                    let value = self.value(other);
                    if value < 0 {
                        continue;
                    }
                    if value > 0 {
                        self.mark_clause_as_garbage(c);
                        break;
                    }
                    if self.marks[widen(other)] == 0 {
                        subset = false;
                        break;
                    }
                }
                if subset && !self.clauses.arena.garbage(c) {
                    found = true;
                    break;
                }
            }
        }
        for &lit in &closure.lits {
            self.marks[widen(lit)] = 0;
        }
        found
    }

    fn extract_xor_gates_with_base_clause(&mut self, closure: &mut Closure, c: Ref) {
        let size_limit = self.option_u32(Opt::Congruencexorarity).min(MAX_ARITY) + 1;
        closure.lits.clear();
        let mut negated_count = 0;
        let mut largest: Option<u32> = None;
        for position in 0..self.clauses.arena.size(c) {
            let lit = self.clauses.arena.lit(c, position);
            let value = self.value(lit);
            if value < 0 {
                continue;
            }
            if value > 0 {
                self.mark_clause_as_garbage(c);
                return;
            }
            if narrow(closure.lits.len()) == size_limit {
                return;
            }
            match largest {
                None => largest = Some(lit),
                Some(prev) if lit > prev => {
                    if negated(prev) {
                        return;
                    }
                    largest = Some(lit);
                }
                Some(_) => {}
            }
            if negated(lit) && largest.is_some_and(|largest| lit < largest) {
                return;
            }
            if negated(lit) {
                negated_count += 1;
                if negated_count > 1 {
                    return;
                }
            }
            closure.lits.push(lit);
        }
        let size = narrow(closure.lits.len());
        if size < SMALLEST_GATE_CLAUSE {
            return;
        }
        let arity = size - 1;
        let needed = 1_u32 << (arity - 1);
        for &lit in &closure.lits {
            if closure.largecount[widen(lit)] < needed
                || closure.largecount[widen(not(lit))] < needed
            {
                return;
            }
        }
        let parity = negated_count;
        for i in 0..1_u32 << arity {
            while i > 0 && parity_lits(&closure.lits) != parity {
                inc_lits(&mut closure.lits);
            }
            if i > 0 && !self.find_large_xor_side_clause(closure) {
                return;
            }
            inc_lits(&mut closure.lits);
        }
        while parity_lits(&closure.lits) != parity {
            inc_lits(&mut closure.lits);
        }
        if parity != 0 {
            if let Some(lit) = closure.lits.iter_mut().find(|lit| negated(**lit)) {
                *lit = not(*lit);
            }
        }
        for position in 0..closure.lits.len() {
            let lit = closure.lits[position];
            let lhs = if parity == 0 { not(lit) } else { lit };
            let _ = self.new_xor_gate(closure, lhs);
            if self.inconsistent {
                break;
            }
        }
    }

    fn unassigned_size(&mut self, c: Ref, limit: u32) -> Option<u32> {
        let mut size = 0;
        for position in 0..self.clauses.arena.size(c) {
            let value = self.value(self.clauses.arena.lit(c, position));
            if value < 0 {
                continue;
            }
            if value > 0 {
                self.mark_clause_as_garbage(c);
                return None;
            }
            if size == limit {
                return None;
            }
            size += 1;
        }
        Some(size)
    }

    fn init_xor_gate_extraction(&mut self, closure: &mut Closure) -> Vec<Ref> {
        let size_limit = self.option_u32(Opt::Congruencexorarity) + 1;
        let lits = widen(2 * self.vars);
        let mut largecount = vec![0_u32; lits];
        let mut candidates = Vec::new();
        for c in self.irredundant_clauses() {
            let Some(size) = self.unassigned_size(c, size_limit) else {
                continue;
            };
            if size < SMALLEST_GATE_CLAUSE {
                continue;
            }
            for &lit in self.clauses.arena.lits(c) {
                if self.value(lit) == 0 {
                    largecount[widen(lit)] += 1;
                }
            }
            candidates.push(c);
        }
        for _ in 0..self.option_u32(Opt::Congruencexorcounts) {
            let mut new_largecount = vec![0_u32; lits];
            let before = candidates.len();
            candidates.retain(|&c| {
                let lits = self.clauses.arena.lits(c);
                let size = narrow(lits.iter().filter(|&&lit| self.value(lit) == 0).count());
                let needed = 1_u32 << (size - 2);
                if lits.iter().any(|&lit| largecount[widen(lit)] < needed) {
                    return false;
                }
                for &lit in lits {
                    if self.value(lit) == 0 {
                        new_largecount[widen(lit)] += 1;
                    }
                }
                true
            });
            largecount = new_largecount;
            if candidates.len() == before {
                break;
            }
        }
        closure.largecount = largecount;
        for &c in &candidates {
            self.connect_clause(c);
        }
        candidates
    }

    fn extract_xor_gates(&mut self, closure: &mut Closure) {
        if self.option(Opt::Congruencexors) == 0 {
            return;
        }
        for c in self.init_xor_gate_extraction(closure) {
            if self.terminated() || self.inconsistent {
                break;
            }
            if self.clauses.arena.garbage(c) {
                continue;
            }
            self.extract_xor_gates_with_base_clause(closure, c);
        }
        for watches in &mut self.clauses.watches {
            watches.clear();
        }
    }

    fn init_ite_gate_extraction(&mut self, closure: &mut Closure) {
        let mut largecount = vec![0_u32; widen(2 * self.vars)];
        let mut ternary = Vec::new();
        for c in self.irredundant_clauses() {
            if self.unassigned_size(c, SMALLEST_GATE_CLAUSE) != Some(SMALLEST_GATE_CLAUSE) {
                continue;
            }
            ternary.push(c);
            for &lit in self.clauses.arena.lits(c) {
                if self.value(lit) == 0 {
                    largecount[widen(lit)] += 1;
                }
            }
        }
        for c in ternary {
            let mut twice = 0;
            let mut connected = true;
            for &lit in self.clauses.arena.lits(c) {
                if self.value(lit) != 0 {
                    continue;
                }
                let count_not_lit = largecount[widen(not(lit))];
                if count_not_lit == 0 {
                    connected = false;
                    break;
                }
                if largecount[widen(lit)] > 1 && count_not_lit > 1 {
                    twice += 1;
                }
            }
            if connected && twice >= 2 {
                self.connect_clause(c);
            }
        }
        closure.largecount = largecount;
    }

    fn copy_conditional_equivalences(&self, lit: u32) -> Vec<[u32; 2]> {
        large_occurrences(&self.clauses.watches[widen(lit)])
            .map(|c| {
                let mut others = self
                    .clauses
                    .arena
                    .lits(c)
                    .iter()
                    .copied()
                    .filter(|&other| other != lit && self.value(other) == 0);
                let first = others.next().unwrap_or(lit);
                let second = others.next().unwrap_or(lit);
                [first.min(second), first.max(second)]
            })
            .collect()
    }

    fn find_conditional_equivalences(&self, lit: u32) -> Vec<[u32; 2]> {
        let mut condbin = self.copy_conditional_equivalences(lit);
        sort_pairs(&mut condbin);
        let mut condeq = Vec::new();
        extract_condeq_pairs(&condbin, &mut condeq);
        sort_pairs(&mut condeq);
        condeq
    }

    fn merge_condeq(
        &mut self,
        closure: &mut Closure,
        cond: u32,
        condeq: &[[u32; 2]],
        not_condeq: &[[u32; 2]],
    ) {
        let mut q = 0;
        for &[lhs, then_lit] in condeq {
            while q < not_condeq.len() && not_condeq[q][0] < lhs {
                q += 1;
            }
            let mut q2 = q;
            while q2 < not_condeq.len() && not_condeq[q2][0] == lhs {
                let else_lit = not_condeq[q2][1];
                q2 += 1;
                self.new_ite_gate(closure, lhs, cond, then_lit, else_lit);
                if self.inconsistent {
                    return;
                }
            }
        }
    }

    fn extract_ite_gates_of_variable(&mut self, closure: &mut Closure, idx: u32) {
        let lit = 2 * idx;
        let not_lit = not(lit);
        let (lit, not_lit) = if self.clauses.watches[widen(lit)].len()
            <= self.clauses.watches[widen(not_lit)].len()
        {
            (lit, not_lit)
        } else {
            (not_lit, lit)
        };
        if self.clauses.watches[widen(lit)].len() <= 1 {
            return;
        }
        let condeq = self.find_conditional_equivalences(lit);
        if condeq.is_empty() {
            return;
        }
        let not_condeq = self.find_conditional_equivalences(not_lit);
        if not_condeq.is_empty() {
            return;
        }
        if negated(lit) {
            self.merge_condeq(closure, not_lit, &condeq, &not_condeq);
        } else {
            self.merge_condeq(closure, lit, &not_condeq, &condeq);
        }
    }

    fn extract_ite_gates(&mut self, closure: &mut Closure) {
        if self.option(Opt::Congruenceites) == 0 {
            return;
        }
        self.init_ite_gate_extraction(closure);
        for idx in 0..self.vars {
            if self.terminated() {
                break;
            }
            if self.active[widen(idx)] {
                self.extract_ite_gates_of_variable(closure, idx);
                if self.inconsistent {
                    break;
                }
            }
        }
        for watches in &mut self.clauses.watches {
            watches.clear();
        }
    }

    fn extract_gates(&mut self, closure: &mut Closure) {
        self.enter_dense_mode(Some(&mut closure.binaries));
        self.extract_binaries(closure);
        self.extract_and_gates(closure);
        if !self.inconsistent && !self.terminated() {
            self.extract_xor_gates(closure);
            if !self.inconsistent && !self.terminated() {
                self.extract_ite_gates(closure);
            }
        }
        let binaries = std::mem::take(&mut closure.binaries);
        self.resume_sparse_mode(Rewatch::All, &binaries);
    }

    fn find_units(&mut self, closure: &mut Closure) {
        closure.units = self.assignment.propagate;
        let mut marked = Vec::new();
        for idx in 0..self.vars {
            'restart: loop {
                if !self.active[widen(idx)] {
                    break;
                }
                for lit in [2 * idx, 2 * idx + 1] {
                    let mut unit = false;
                    for other in leading_binaries(&self.clauses.watches[widen(lit)]) {
                        if self.marks[widen(not(other))] != 0 {
                            unit = true;
                            break;
                        }
                        if self.marks[widen(other)] == 0 {
                            self.marks[widen(other)] = TRUE;
                            marked.push(other);
                        }
                    }
                    for other in marked.drain(..) {
                        self.marks[widen(other)] = 0;
                    }
                    if unit {
                        if !self.learn_congruence_unit(lit) {
                            return;
                        }
                        continue 'restart;
                    }
                }
                break;
            }
        }
    }

    fn find_equivalences(&mut self, closure: &mut Closure) {
        let mut marked = Vec::new();
        for idx in 0..self.vars {
            'restart: loop {
                if !self.active[widen(idx)] {
                    break;
                }
                let lit = 2 * idx;
                for other in leading_binaries(&self.clauses.watches[widen(lit)]) {
                    if lit < other && self.marks[widen(other)] == 0 {
                        self.marks[widen(other)] = TRUE;
                        marked.push(other);
                    }
                }
                if marked.is_empty() {
                    break;
                }
                let not_lit = not(lit);
                let others: Vec<u32> =
                    leading_binaries(&self.clauses.watches[widen(not_lit)]).collect();
                for other in others {
                    if not_lit > other || lit == other || self.marks[widen(not(other))] == 0 {
                        continue;
                    }
                    if closure.find_repr(lit) != closure.find_repr(other) {
                        let _ = self.merge_literals(closure, lit, other);
                        for other in marked.drain(..) {
                            self.marks[widen(other)] = 0;
                        }
                        if self.inconsistent {
                            return;
                        }
                        continue 'restart;
                    }
                }
                for other in marked.drain(..) {
                    self.marks[widen(other)] = 0;
                }
                break;
            }
        }
    }

    fn simplify_gates(&mut self, closure: &mut Closure, lit: u32) -> bool {
        let occurrences = std::mem::take(&mut closure.occurrences[widen(lit)]);
        for g in occurrences {
            if !self.simplify_gate(closure, g) {
                return false;
            }
        }
        true
    }

    fn rewrite_gates(&mut self, closure: &mut Closure, dst: u32, src: u32) -> bool {
        let occurrences = std::mem::take(&mut closure.occurrences[widen(src)]);
        for g in occurrences {
            if !self.rewrite_gate(closure, g, dst, src) {
                return false;
            }
            if !closure.gates[g].garbage && closure.gates[g].rhs.contains(&dst) {
                closure.occurrences[widen(dst)].push(g);
            }
        }
        true
    }

    fn propagate_units_and_equivalences(&mut self, closure: &mut Closure) -> usize {
        let mut propagated = 0;
        loop {
            if self.terminated() {
                return propagated;
            }
            while closure.units < self.assignment.trail.len() {
                let lit = self.assignment.trail[closure.units];
                closure.units += 1;
                if !self.simplify_gates(closure, lit) || !self.simplify_gates(closure, not(lit)) {
                    return propagated;
                }
            }
            let Some(lit) = closure.schedule.pop_front() else {
                return propagated;
            };
            closure.scheduled[widen(idx(lit))] = false;
            propagated += 1;
            if self.value(lit) != 0 {
                continue;
            }
            let repr = closure.find_repr(lit);
            if !self.rewrite_gates(closure, repr, lit)
                || !self.rewrite_gates(closure, not(repr), not(lit))
            {
                return propagated;
            }
        }
    }

    fn flush_closure_units(&mut self) {
        if !self.inconsistent && self.unflushed > 0 {
            self.assignment.trail.clear();
            self.assignment.propagate = 0;
            self.unflushed = 0;
        }
    }

    fn find_subsuming_clause(&mut self, closure: &Closure, c: Ref) -> bool {
        for position in 0..self.clauses.arena.size(c) {
            let repr = closure.find_repr(self.clauses.arena.lit(c, position));
            if self.value(repr) == 0 {
                self.marks[widen(repr)] = TRUE;
            }
        }
        let mut least = None;
        let mut least_count = usize::MAX;
        let mut subsumed = false;
        'search: for position in 0..self.clauses.arena.size(c) {
            let repr_lit = closure.find_repr(self.clauses.arena.lit(c, position));
            let watches = &self.clauses.watches[widen(repr_lit)];
            if watches.len() < least_count {
                least_count = watches.len();
                least = Some(repr_lit);
            }
            for d in large_occurrences(watches) {
                if !self.clauses.arena.redundant(c) && self.clauses.arena.redundant(d) {
                    continue;
                }
                let covered = self.clauses.arena.lits(d).iter().all(|&other| {
                    self.value(other) < 0 || self.marks[widen(closure.find_repr(other))] != 0
                });
                if covered {
                    subsumed = true;
                    break 'search;
                }
            }
        }
        for position in 0..self.clauses.arena.size(c) {
            let repr = closure.find_repr(self.clauses.arena.lit(c, position));
            if self.value(repr) == 0 {
                self.marks[widen(repr)] = 0;
            }
        }
        if subsumed {
            self.mark_clause_as_garbage(c);
        } else if let Some(least) = least {
            self.clauses.watches[widen(least)].push(watch::large(c));
        }
        subsumed
    }

    fn forward_subsume_matching_clauses(&mut self, closure: &Closure) {
        self.flush_closure_units();
        let mut binaries = Vec::new();
        self.enter_dense_mode(Some(&mut binaries));
        let mut matchable = vec![false; widen(self.vars)];
        for var in 0..self.vars {
            if !self.active[widen(var)] {
                continue;
            }
            let lit = 2 * var;
            let repr = closure.find_repr(lit);
            if lit != repr {
                matchable[widen(var)] = true;
                matchable[widen(idx(repr))] = true;
            }
        }
        let mut candidates = Vec::new();
        let mut marked = Vec::new();
        let clauses: Vec<Ref> = self
            .clauses
            .arena
            .refs()
            .take_while(|&at| self.clauses.last_irredundant.is_none_or(|last| at <= last))
            .collect();
        for c in clauses {
            if self.clauses.arena.garbage(c) {
                continue;
            }
            let mut contains_matchable = false;
            for position in 0..self.clauses.arena.size(c) {
                let lit = self.clauses.arena.lit(c, position);
                let value = self.value(lit);
                if value < 0 {
                    continue;
                }
                if value > 0 {
                    self.mark_clause_as_garbage(c);
                    break;
                }
                contains_matchable |= matchable[widen(idx(lit))];
                let repr = closure.find_repr(lit);
                if self.marks[widen(repr)] != 0 {
                    continue;
                }
                if self.marks[widen(not(repr))] != 0 {
                    self.mark_clause_as_garbage(c);
                    break;
                }
                self.marks[widen(repr)] = TRUE;
                marked.push(repr);
            }
            let size = marked.len();
            for repr in marked.drain(..) {
                self.marks[widen(repr)] = 0;
            }
            if !self.clauses.arena.garbage(c) && contains_matchable {
                candidates.push((c, size));
            }
        }
        candidates.sort_by_key(|&(_, size)| size);
        for (c, _) in candidates {
            if self.terminated() {
                break;
            }
            let _ = self.find_subsuming_clause(closure, c);
        }
        self.resume_sparse_mode(Rewatch::All, &binaries);
    }

    pub(crate) fn congruence(&mut self) -> bool {
        if self.inconsistent
            || self.option(Opt::Congruence) == 0
            || self.option(Opt::Congruenceands) == 0
                && self.option(Opt::Congruenceites) == 0
                && self.option(Opt::Congruencexors) == 0
            || self.option(Opt::Congruenceonce) != 0 && self.statistics.closures > 0
            || self.terminated()
            || self.congruence_delay.delaying()
        {
            return false;
        }
        self.statistics.closures += 1;
        let lits = 2 * self.vars;
        let mut random = self.random;
        let mut nonces = [0; SIZE_NONCES];
        for nonce in &mut nonces {
            *nonce = 1 | random.next64();
        }
        let mut closure = Closure {
            scheduled: vec![false; widen(self.vars)],
            occurrences: vec![Vec::new(); widen(lits)],
            gates: Vec::new(),
            lits: Vec::new(),
            binaries: Vec::new(),
            schedule: VecDeque::new(),
            repr: (0..lits).collect(),
            table: Vec::new(),
            entries: 0,
            nonces,
            units: 0,
            negbincount: Vec::new(),
            largecount: Vec::new(),
            chain: Vec::new(),
        };
        self.extract_gates(&mut closure);
        let mut reset = false;
        if !self.inconsistent && !self.terminated() {
            self.find_units(&mut closure);
            if !self.inconsistent && !self.terminated() {
                self.find_equivalences(&mut closure);
                if !self.inconsistent && !self.terminated() {
                    let propagated = self.propagate_units_and_equivalences(&mut closure);
                    if !self.inconsistent && propagated > 0 && !self.terminated() {
                        self.forward_subsume_matching_clauses(&closure);
                        reset = true;
                    }
                }
            }
        }
        if !reset {
            self.flush_closure_units();
        }
        let equivalent = (0..self.vars)
            .filter(|&idx| {
                let lit = 2 * idx;
                self.value(lit) == 0 && closure.repr[widen(lit)] != lit
            })
            .count();
        let active = real(u64::from(self.active_count));
        let rate = if active == 0.0 {
            0.0
        } else {
            real(u64::try_from(equivalent).unwrap_or(u64::MAX)) / active
        };
        if rate < MIN_EQUIVALENT_RATE {
            self.congruence_delay.bump();
        } else {
            self.congruence_delay.reduce();
        }
        equivalent > 0
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Chain {
    None,
    Xor,
    TurnedIte,
}

impl Solver {
    fn simplify_and_add_to_proof_chain(&mut self, unsimplified: &[u32], chain: &mut Vec<u32>) {
        let mut clause: Vec<u32> = Vec::new();
        for &lit in unsimplified {
            if clause.contains(&lit) {
                continue;
            }
            if clause.contains(&not(lit)) {
                return;
            }
            clause.push(lit);
        }
        self.proof_lits(ProofStep::Add, &clause);
        chain.extend_from_slice(&clause);
        chain.push(INVALID_LIT);
    }

    fn add_xor_matching_proof_chain(
        &mut self,
        closure: &mut Closure,
        g: usize,
        lhs1: u32,
        lhs2: u32,
    ) {
        if lhs1 == lhs2 || self.proof.is_none() {
            return;
        }
        let rhs = &closure.gates[g].rhs;
        let mut unsimplified = rhs[..rhs.len() - 1].to_vec();
        let mut chain = std::mem::take(&mut closure.chain);
        loop {
            let size = unsimplified.len();
            for _ in 0..1_u64 << size {
                unsimplified.extend([not(lhs1), lhs2]);
                self.simplify_and_add_to_proof_chain(&unsimplified, &mut chain);
                unsimplified.truncate(size);
                unsimplified.extend([lhs1, not(lhs2)]);
                self.simplify_and_add_to_proof_chain(&unsimplified, &mut chain);
                unsimplified.truncate(size);
                inc_lits(&mut unsimplified);
            }
            let _ = unsimplified.pop();
            if unsimplified.is_empty() {
                break;
            }
        }
        closure.chain = chain;
    }

    fn add_ite_matching_proof_chain(
        &mut self,
        closure: &mut Closure,
        g: usize,
        lhs1: u32,
        lhs2: u32,
    ) {
        if lhs1 == lhs2 || self.proof.is_none() {
            return;
        }
        let cond = closure.gates[g].rhs[0];
        let mut chain = std::mem::take(&mut closure.chain);
        for (first, second) in [(lhs1, not(lhs2)), (not(lhs1), lhs2)] {
            self.simplify_and_add_to_proof_chain(&[first, second, cond], &mut chain);
            self.simplify_and_add_to_proof_chain(&[first, second, not(cond)], &mut chain);
            if first == lhs1 {
                self.proof_lits(ProofStep::Add, &[first, second]);
                chain.extend([first, second, INVALID_LIT]);
            } else {
                self.simplify_and_add_to_proof_chain(&[first, second], &mut chain);
            }
        }
        closure.chain = chain;
    }

    fn add_ite_turned_and_binary_clauses(&mut self, closure: &mut Closure, g: usize) {
        if self.proof.is_none() {
            return;
        }
        let not_lhs = not(closure.gates[g].lhs);
        let [first, second] = [closure.gates[g].rhs[0], closure.gates[g].rhs[1]];
        let mut chain = std::mem::take(&mut closure.chain);
        self.simplify_and_add_to_proof_chain(&[not_lhs, first], &mut chain);
        self.simplify_and_add_to_proof_chain(&[not_lhs, second], &mut chain);
        closure.chain = chain;
    }

    fn add_xor_shrinking_proof_chain(&mut self, rhs: &[u32], lhs: u32, pivot: u32) {
        if self.proof.is_none() {
            return;
        }
        let mut clause = rhs.to_vec();
        clause.push(not(lhs));
        let parity = not(lhs) & 1;
        let size = clause.len();
        for round in 0..1_u64 << size {
            while round > 0 && parity != parity_lits(&clause) {
                inc_lits(&mut clause);
            }
            for extra in [Some(pivot), Some(not(pivot)), None] {
                let mut lits = clause.clone();
                lits.extend(extra);
                self.proof_lits(ProofStep::Add, &lits);
            }
            for extra in [pivot, not(pivot)] {
                let mut lits = clause.clone();
                lits.push(extra);
                self.proof_lits(ProofStep::Delete, &lits);
            }
            inc_lits(&mut clause);
        }
    }

    fn delete_proof_chain(&mut self, closure: &mut Closure) {
        if self.proof.is_none() {
            closure.chain.clear();
            return;
        }
        let chain = std::mem::take(&mut closure.chain);
        for clause in chain.split(|&lit| lit == INVALID_LIT) {
            if !clause.is_empty() {
                self.proof_lits(ProofStep::Delete, clause);
            }
        }
    }
}
