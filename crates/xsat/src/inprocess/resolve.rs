use crate::{
    options::Opt,
    solver::{literal, not, Solver},
    store::{
        arena::{Ref, INVALID_LIT},
        convert::widen,
        watch::{self, Occurrence},
    },
    trace::proof::Step,
};

const TOO_LONG: u32 = u32::MAX;

#[derive(Clone, Copy, Debug)]
enum Antecedent {
    Binary([u32; 2]),
    Large(Ref),
}

impl Solver {
    fn antecedent(lit: u32, word: u32) -> Antecedent {
        match watch::occurrence(word) {
            Occurrence::Binary(other) => Antecedent::Binary([lit, other]),
            Occurrence::Large(at) => Antecedent::Large(at),
        }
    }

    fn antecedent_size(&self, antecedent: Antecedent) -> u32 {
        match antecedent {
            Antecedent::Binary(_) => 2,
            Antecedent::Large(at) => self.clauses.arena.size(at),
        }
    }

    fn antecedent_lit(&self, antecedent: Antecedent, position: u32) -> u32 {
        match antecedent {
            Antecedent::Binary(lits) => lits[widen(position)],
            Antecedent::Large(at) => self.clauses.arena.lit(at, position),
        }
    }

    fn antecedent_garbage(&self, antecedent: Antecedent) -> bool {
        match antecedent {
            Antecedent::Binary(_) => false,
            Antecedent::Large(at) => self.clauses.arena.garbage(at),
        }
    }

    fn eliminate_antecedent(&mut self, antecedent: Antecedent, other: u32) {
        if let Antecedent::Large(at) = antecedent {
            self.eliminate_clause(at, other);
        }
    }

    fn occurrences_literal(&mut self, lit: u32) -> (u32, bool) {
        let clslim = self.option_u32(Opt::Eliminateclslim);
        let mut watches = std::mem::take(&mut self.clauses.watches[widen(lit)]);
        let end = watches.len();
        let (mut p, mut q) = (0, 0);
        let mut res = 0;
        let mut failed = false;
        while p < end {
            let word = watches[p];
            watches[q] = word;
            p += 1;
            q += 1;
            match watch::occurrence(word) {
                Occurrence::Binary(other) => {
                    if self.value(other) > 0 {
                        self.eliminate_binary(lit, other);
                        q -= 1;
                    } else {
                        res += 1;
                    }
                }
                Occurrence::Large(at) => {
                    if self.clauses.arena.garbage(at) {
                        q -= 1;
                    } else if self.clauses.arena.size(at) > clslim {
                        failed = true;
                        break;
                    } else {
                        res += 1;
                    }
                }
            }
        }
        watches.copy_within(p..end, q);
        watches.truncate(q + end - p);
        let dropped = watches.len() != end;
        self.clauses.watches[widen(lit)] = watches;
        if failed {
            (TOO_LONG, false)
        } else {
            (res, dropped)
        }
    }

    fn push_second_antecedent(&mut self, not_lit: u32, d: Antecedent) -> bool {
        for position in 0..self.antecedent_size(d) {
            let other = self.antecedent_lit(d, position);
            if other == not_lit {
                continue;
            }
            let value = self.value(other);
            if value < 0 {
                continue;
            }
            if value > 0 {
                self.eliminate_antecedent(d, other);
                return false;
            }
            if self.marks[widen(other)] != 0 {
                continue;
            }
            if self.marks[widen(not(other))] != 0 {
                return false;
            }
            self.elimination.resolvents.push(other);
        }
        true
    }

    fn resolve_antecedents(
        &mut self,
        lit: u32,
        first: &[u32],
        second: &[u32],
        resolved: &mut u64,
        limit: u64,
    ) -> bool {
        let not_lit = not(lit);
        let clslim = widen(self.option_u32(Opt::Eliminateclslim));
        let mut failed = false;
        for &word0 in first {
            let c = Solver::antecedent(lit, word0);
            if self.antecedent_garbage(c) {
                continue;
            }
            let size = self.antecedent_size(c);
            let mut satisfied = false;
            for position in 0..size {
                let other = self.antecedent_lit(c, position);
                if other == lit {
                    continue;
                }
                let value = self.value(other);
                if value > 0 {
                    satisfied = true;
                    self.eliminate_antecedent(c, other);
                    break;
                }
            }
            if satisfied {
                continue;
            }
            for position in 0..size {
                let other = self.antecedent_lit(c, position);
                if other != lit {
                    self.marks[widen(other)] = 1;
                }
            }
            for &word1 in second {
                let d = Solver::antecedent(not_lit, word1);
                if self.antecedent_garbage(d) {
                    continue;
                }
                let saved = self.elimination.resolvents.len();
                self.statistics.eliminate_resolutions += 1;
                if !self.push_second_antecedent(not_lit, d) {
                    self.elimination.resolvents.truncate(saved);
                    continue;
                }
                *resolved += 1;
                if *resolved > limit {
                    failed = true;
                    break;
                }
                for position in 0..size {
                    let other = self.antecedent_lit(c, position);
                    if other != lit && self.value(other) == 0 {
                        self.elimination.resolvents.push(other);
                    }
                }
                let resolvent = self.elimination.resolvents.len() - saved;
                if resolvent == 0 {
                    self.inconsistent = true;
                    self.proof_lits(Step::Add, &[]);
                    failed = true;
                    break;
                }
                if resolvent == 1 {
                    let unit = self.elimination.resolvents[saved];
                    self.learned_unit(unit);
                    self.elimination.resolvents.truncate(saved);
                    if self.marks[widen(unit)] <= 0 {
                        continue;
                    }
                    break;
                }
                if resolvent > clslim {
                    failed = true;
                    break;
                }
                self.elimination.resolvents.push(INVALID_LIT);
            }
            for position in 0..size {
                let other = self.antecedent_lit(c, position);
                if other != lit {
                    self.marks[widen(other)] = 0;
                }
            }
            if failed {
                break;
            }
        }
        !failed
    }

    pub(crate) fn generate_resolvents(&mut self, idx: u32) -> Option<u32> {
        let mut lit = literal(idx);
        let mut not_lit = not(lit);
        let (mut pos_count, pos_dropped) = self.occurrences_literal(lit);
        let (mut neg_count, neg_dropped) = self.occurrences_literal(not_lit);
        let update = pos_dropped || neg_dropped;
        if pos_count > neg_count {
            std::mem::swap(&mut lit, &mut not_lit);
            std::mem::swap(&mut pos_count, &mut neg_count);
        }
        let occlim = u64::from(self.option_u32(Opt::Eliminateocclim));
        let mut limit = u64::from(pos_count) + u64::from(neg_count);
        if pos_count == 0 {
            return Some(lit);
        }
        if limit > occlim {
            return None;
        }
        limit += u64::from(self.elimination.bound);
        let gates = self.find_gates(lit);
        if self.value(lit) != 0 {
            self.elimination.gates = [Vec::new(), Vec::new()];
            return None;
        }
        self.get_antecedents(lit);
        let [gates0, gates1] = std::mem::take(&mut self.elimination.gates);
        let [antecedents0, antecedents1] = std::mem::take(&mut self.elimination.antecedents);
        let mut resolved = 0;
        let resolved_all = if gates {
            self.resolve_antecedents(lit, &gates0, &antecedents1, &mut resolved, limit)
                && self.resolve_antecedents(not_lit, &gates1, &antecedents0, &mut resolved, limit)
                && (!self.elimination.resolve_gate
                    || self.resolve_antecedents(lit, &gates0, &gates1, &mut resolved, limit))
        } else {
            self.resolve_antecedents(lit, &antecedents0, &antecedents1, &mut resolved, limit)
        };
        if !resolved_all {
            self.elimination.resolvents.clear();
            if update {
                self.update_variable_score(idx);
            }
            return None;
        }
        Some(lit)
    }
}
