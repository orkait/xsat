use crate::{
    inprocess::gates::Side,
    options::Opt,
    solver::{idx, not, Solver},
    store::{
        arena::{Ref, INVALID_LIT},
        convert::widen,
        watch::{self, Occurrence},
    },
};

impl Solver {
    fn ternary_clause(&mut self, at: Ref) -> Option<[u32; 3]> {
        if self.clauses.arena.garbage(at) {
            return None;
        }
        let mut found = [INVALID_LIT; 3];
        let mut count = 0;
        for position in 0..self.clauses.arena.size(at) {
            let other = self.clauses.arena.lit(at, position);
            let value = self.value(other);
            if value > 0 {
                self.eliminate_clause(at, INVALID_LIT);
                return None;
            }
            if value < 0 {
                continue;
            }
            *found.get_mut(count)? = other;
            count += 1;
        }
        (count == found.len()).then_some(found)
    }

    fn match_ternary_ref(&mut self, at: Ref, lits: [u32; 3]) -> bool {
        if self.clauses.arena.garbage(at) {
            return false;
        }
        let mut found = 0;
        for position in 0..self.clauses.arena.size(at) {
            let other = self.clauses.arena.lit(at, position);
            let value = self.value(other);
            if value > 0 {
                self.eliminate_clause(at, INVALID_LIT);
                return false;
            }
            if value < 0 {
                continue;
            }
            if !lits.contains(&other) {
                return false;
            }
            found += 1;
        }
        if found != lits.len() {
            self.elimination.resolve_gate = true;
        }
        true
    }

    fn match_ternary_watch(&mut self, word: u32, lits: [u32; 3]) -> bool {
        match watch::occurrence(word) {
            Occurrence::Binary(other) => {
                if other != lits[1] && other != lits[2] {
                    return false;
                }
                self.elimination.resolve_gate = true;
                true
            }
            Occurrence::Large(at) => self.match_ternary_ref(at, lits),
        }
    }

    fn find_ternary_clause(&mut self, steps: &mut u64, lits: [u32; 3]) -> Option<usize> {
        let a = widen(lits[0]);
        for position in 0..self.clauses.watches[a].len() {
            *steps += 1;
            if self.match_ternary_watch(self.clauses.watches[a][position], lits) {
                return Some(position);
            }
        }
        None
    }

    fn ternary_with(&mut self, lit: u32, word: u32) -> Option<[u32; 3]> {
        let Occurrence::Large(at) = watch::occurrence(word) else {
            return None;
        };
        let [mut a, mut b, mut c] = self.ternary_clause(at)?;
        if b == lit {
            std::mem::swap(&mut a, &mut b);
        }
        if c == lit {
            std::mem::swap(&mut a, &mut c);
        }
        Some([a, b, c])
    }

    pub(crate) fn find_if_then_else_gate(&mut self, lit: u32, side: Side) -> bool {
        if self.option(Opt::Ifthenelse) == 0 {
            return false;
        }
        let watches = widen(lit);
        let end = self.clauses.watches[watches].len();
        if end == 0 {
            return false;
        }
        let large_clauses = self.clauses.watches[watches]
            .iter()
            .filter(|&&word| matches!(watch::occurrence(word), Occurrence::Large(_)))
            .count();
        let large_clauses = u64::try_from(large_clauses).unwrap_or(u64::MAX);
        let limit = u64::from(self.option_u32(Opt::Eliminateocclim));
        if large_clauses * large_clauses > limit {
            return false;
        }
        let not_lit = not(lit);
        let mut steps = 0;
        let mut p1 = 0;
        while steps < limit && p1 != end - 1 {
            let w1 = self.clauses.watches[watches][p1];
            p1 += 1;
            let Some([_, b1, c1]) = self.ternary_with(lit, w1) else {
                continue;
            };
            let mut p2 = p1;
            while steps < limit && p2 != end {
                let w2 = self.clauses.watches[watches][p2];
                p2 += 1;
                let Some([_, mut b2, mut c2]) = self.ternary_with(lit, w2) else {
                    continue;
                };
                if idx(b1) == idx(c2) {
                    std::mem::swap(&mut b2, &mut c2);
                }
                if idx(c1) == idx(c2) || b1 != not(b2) {
                    continue;
                }
                self.elimination.resolve_gate = false;
                let Some(p3) = self.find_ternary_clause(&mut steps, [not_lit, b1, not(c1)]) else {
                    continue;
                };
                let Some(p4) = self.find_ternary_clause(&mut steps, [not_lit, b2, not(c2)]) else {
                    continue;
                };
                let negative = &self.clauses.watches[widen(not_lit)];
                let (w3, w4) = (negative[p3.min(p4)], negative[p3.max(p4)]);
                self.elimination.gates[side.index()].extend([w1, w2]);
                self.elimination.gates[side.other().index()].extend([w3, w4]);
                return true;
            }
        }
        false
    }
}
