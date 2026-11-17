use crate::{
    solver::{Conflict, Solver},
    store::{
        arena::{Ref, INITIAL_SEARCHED},
        convert::widen,
        watch::{self, Head},
    },
};

const BINARY_ANTECEDENT: u32 = 3;

impl Solver {
    fn large_on_the_fly_strengthen(&mut self, at: Ref, lit: u32) -> Conflict {
        if self.clauses.arena.lit(at, 0) == lit {
            self.clauses.arena.lits_mut(at).swap(0, 1);
        }
        watch::remove_blocking(&mut self.clauses.watches[widen(lit)], at);
        self.proof_shrink_clause(at, lit, self.clauses.arena.lit(at, 0));
        let old_size = self.clauses.arena.size(at);
        let mut new_size = 1;
        for position in 2..old_size {
            let other = self.clauses.arena.lit(at, position);
            if self.level_of(other) == 0 {
                continue;
            }
            self.clauses.arena.set_lit(at, new_size, other);
            new_size += 1;
            if !self.clauses.arena.redundant(at) {
                self.mark_added_literal(other);
            }
        }
        self.clauses.arena.shrink(at, new_size);
        self.clauses.arena.set_searched(at, INITIAL_SEARCHED);
        if self.clauses.arena.redundant(at) && self.clauses.arena.glue(at) >= new_size {
            self.promote_clause(at, new_size - 1);
        }
        let mut highest_position = 1;
        let mut highest_level = self.level_of(self.clauses.arena.lit(at, 1));
        for position in 2..new_size {
            let level = self.level_of(self.clauses.arena.lit(at, position));
            if level > highest_level {
                highest_position = position;
                highest_level = level;
            }
        }
        let lits = self.clauses.arena.lits_mut(at);
        lits.swap(1, widen(highest_position));
        let (first, second) = (lits[0], lits[1]);
        watch::push_blocking(&mut self.clauses.watches[widen(second)], first, at);
        let watches = &mut self.clauses.watches[widen(first)];
        let mut p = 0;
        while p < watches.len() {
            if let Head::Binary(_) = watch::decode(watches[p]) {
                p += 1;
                continue;
            }
            if watches[p + 1] == at.0 {
                watches[p] = watch::blocking(second);
                break;
            }
            p += 2;
        }
        Conflict::Large(at)
    }

    fn binary_on_the_fly_strengthen(&mut self, at: Ref, lit: u32) -> Conflict {
        let mut kept = self
            .clauses
            .arena
            .lits(at)
            .iter()
            .copied()
            .filter(|&other| other != lit && self.level_of(other) > 0);
        let (Some(first), Some(second)) = (kept.next(), kept.next()) else {
            return Conflict::Large(at);
        };
        self.new_binary_clause(first, second);
        for position in 0..2 {
            let watched = self.clauses.arena.lit(at, position);
            watch::remove_blocking(&mut self.clauses.watches[widen(watched)], at);
        }
        self.mark_clause_as_garbage(at);
        Conflict::Binary([first, second])
    }

    pub(crate) fn on_the_fly_strengthen(&mut self, at: Ref, lit: u32) -> Conflict {
        if !self.clauses.arena.redundant(at) {
            self.mark_removed_literal(lit);
        }
        if self.analysis.antecedent_size == BINARY_ANTECEDENT {
            self.binary_on_the_fly_strengthen(at, lit)
        } else {
            self.large_on_the_fly_strengthen(at, lit)
        }
    }

    pub(crate) fn on_the_fly_subsume(&mut self, strengthened: Conflict, at: Ref) {
        self.mark_clause_as_garbage(at);
        let Conflict::Large(kept) = strengthened else {
            return;
        };
        if !self.clauses.arena.redundant(kept) {
            return;
        }
        if self.clauses.arena.redundant(at) {
            let glue = self.clauses.arena.glue(at);
            if self.clauses.arena.glue(kept) > glue {
                self.promote_clause(kept, glue);
            }
            return;
        }
        self.clauses.arena.set_irredundant(kept);
        if self.clauses.last_irredundant.is_none_or(|last| last < kept) {
            self.clauses.last_irredundant = Some(kept);
        }
        self.statistics.clauses_irredundant += 1;
        self.statistics.clauses_redundant -= 1;
    }
}
