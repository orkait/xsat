use crate::{
    inprocess::gates::Side,
    options::Opt,
    solver::{not, Solver},
    store::{
        convert::widen,
        watch::{self, Head},
    },
};

impl Solver {
    pub(crate) fn find_equivalence_gate(&mut self, lit: u32) -> bool {
        if self.option(Opt::Equivalences) == 0 || self.mark_binaries(lit) == 0 {
            return false;
        }
        let not_lit = not(lit);
        let replace = self.clauses.watches[widen(not_lit)]
            .iter()
            .find_map(|&word| match watch::decode(word) {
                Head::Binary(other) if self.marks[widen(not(other))] != 0 => Some(other),
                Head::Binary(_) | Head::Blocking(_) => None,
            });
        self.unmark_binaries(lit);
        let Some(replace) = replace else {
            return false;
        };
        self.elimination.gates[Side::Negative.index()].push(watch::binary(replace));
        self.elimination.gates[Side::Positive.index()].push(watch::binary(not(replace)));
        true
    }
}
