use crate::{
    inprocess::gates::Side,
    options::Opt,
    solver::{not, Solver},
    store::{
        arena::INVALID_LIT,
        convert::widen,
        watch::{self, Head, Occurrence},
    },
};

impl Solver {
    pub(crate) fn find_and_gate(&mut self, lit: u32, side: Side) -> bool {
        if self.option(Opt::Ands) == 0 {
            return false;
        }
        let marked = self.mark_binaries(lit);
        if marked == 0 {
            return false;
        }
        if marked < 2 {
            self.unmark_binaries(lit);
            return false;
        }
        let not_lit = not(lit);
        let mut base = None;
        for position in 0..self.clauses.watches[widen(not_lit)].len() {
            let Occurrence::Large(at) =
                watch::occurrence(self.clauses.watches[widen(not_lit)][position])
            else {
                continue;
            };
            base = Some(at);
            for position in 0..self.clauses.arena.size(at) {
                let other = self.clauses.arena.lit(at, position);
                if other == not_lit {
                    continue;
                }
                let value = self.value(other);
                if value > 0 {
                    self.eliminate_clause(at, INVALID_LIT);
                    base = None;
                    break;
                }
                if value < 0 || self.marks[widen(not(other))] != 0 {
                    continue;
                }
                base = None;
                break;
            }
            if base.is_some() {
                break;
            }
        }
        let Some(base) = base else {
            self.unmark_binaries(lit);
            return false;
        };
        for position in 0..self.clauses.arena.size(base) {
            let other = self.clauses.arena.lit(base, position);
            if other != not_lit && self.value(other) == 0 {
                self.marks[widen(not(other))] = 0;
            }
        }
        for position in 0..self.clauses.watches[widen(lit)].len() {
            if let Head::Binary(other) = watch::decode(self.clauses.watches[widen(lit)][position]) {
                if self.marks[widen(other)] != 0 {
                    self.marks[widen(other)] = 0;
                } else {
                    self.elimination.gates[side.index()].push(watch::binary(other));
                }
            }
        }
        self.elimination.gates[side.other().index()].push(watch::large(base));
        true
    }
}
