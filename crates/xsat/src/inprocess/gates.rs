use crate::{
    options::Opt,
    solver::{not, Solver},
    store::{
        convert::widen,
        watch::{self, Head},
    },
};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Side {
    Positive,
    Negative,
}

impl Side {
    pub(crate) const fn index(self) -> usize {
        match self {
            Side::Positive => 0,
            Side::Negative => 1,
        }
    }

    pub(crate) const fn other(self) -> Side {
        match self {
            Side::Positive => Side::Negative,
            Side::Negative => Side::Positive,
        }
    }
}

impl Solver {
    pub(crate) fn mark_binaries(&mut self, lit: u32) -> usize {
        let mut res = 0;
        for position in 0..self.clauses.watches[widen(lit)].len() {
            if let Head::Binary(other) = watch::decode(self.clauses.watches[widen(lit)][position]) {
                if self.marks[widen(other)] == 0 {
                    self.marks[widen(other)] = 1;
                    res += 1;
                }
            }
        }
        res
    }

    pub(crate) fn unmark_binaries(&mut self, lit: u32) {
        for position in 0..self.clauses.watches[widen(lit)].len() {
            if let Head::Binary(other) = watch::decode(self.clauses.watches[widen(lit)][position]) {
                self.marks[widen(other)] = 0;
            }
        }
    }

    pub(crate) fn find_gates(&mut self, lit: u32) -> bool {
        self.elimination.resolve_gate = false;
        if self.option(Opt::Extract) == 0 {
            return false;
        }
        let not_lit = not(lit);
        if self.clauses.watches[widen(not_lit)].is_empty() {
            return false;
        }
        self.find_equivalence_gate(lit)
            || self.find_and_gate(lit, Side::Positive)
            || self.find_and_gate(not_lit, Side::Negative)
            || self.find_if_then_else_gate(lit, Side::Positive)
            || self.find_if_then_else_gate(not_lit, Side::Negative)
            || self.find_definition(lit)
    }

    fn get_side_antecedents(&mut self, lit: u32, side: Side) {
        let gates = &self.elimination.gates[side.index()];
        let mut next = 0;
        let mut antecedents = Vec::new();
        for &word in &self.clauses.watches[widen(lit)] {
            if gates.get(next) == Some(&word) {
                next += 1;
            } else {
                antecedents.push(word);
            }
        }
        self.elimination.antecedents[side.index()] = antecedents;
    }

    pub(crate) fn get_antecedents(&mut self, lit: u32) {
        self.get_side_antecedents(lit, Side::Positive);
        self.get_side_antecedents(not(lit), Side::Negative);
    }
}
