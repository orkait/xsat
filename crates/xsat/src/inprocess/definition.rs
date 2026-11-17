use crate::{
    inprocess::{
        gates::Side,
        kitten::{Origin, Status},
    },
    options::Opt,
    solver::{not, Solver},
    store::{
        arena::INVALID_LIT,
        convert::widen,
        watch::{self, Occurrence},
    },
    trace::proof::Step,
};

const CORE_TICKS_FACTOR: u64 = 10;
const FIRST_CORE: i32 = 2;

impl Solver {
    fn trace_one_sided_core_lemmas(&mut self, unit: u32, core: &[(Origin, Vec<u32>)]) {
        let mut lemmas: Vec<Vec<u32>> = Vec::new();
        for (origin, lits) in core {
            if *origin != Origin::Learned {
                continue;
            }
            if lits.is_empty() {
                self.learned_unit(unit);
                for lemma in lemmas.drain(..) {
                    self.proof_lits(Step::Delete, &lemma);
                }
            } else {
                let mut lemma = vec![unit];
                lemma.extend_from_slice(lits);
                self.proof_lits(Step::Add, &lemma);
                lemmas.push(lemma);
            }
        }
    }

    pub(crate) fn find_definition(&mut self, lit: u32) -> bool {
        if self.option(Opt::Definitions) == 0 {
            return false;
        }
        let Some(mut kitten) = self.kitten.take() else {
            return false;
        };
        kitten.clear();
        kitten.track_antecedents();
        let not_lit = not(lit);
        let mut exported = 0;
        for except in [lit, not_lit] {
            for &word in &self.clauses.watches[widen(except)] {
                match watch::occurrence(word) {
                    Occurrence::Binary(other) => {
                        kitten.clause_with_id_and_exception(exported, &[other], INVALID_LIT);
                    }
                    Occurrence::Large(at) => {
                        kitten.clause_with_id_and_exception(
                            exported,
                            self.clauses.arena.lits(at),
                            except,
                        );
                    }
                }
                exported += 1;
            }
        }
        let limit = u64::from(self.option_u32(Opt::Definitionticks));
        kitten.set_ticks_limit(limit);
        let mut res = false;
        if kitten.solve() == Status::Unsatisfiable {
            let _ = kitten.compute_clausal_core();
            let mut cored = true;
            for _ in FIRST_CORE..=self.option(Opt::Definitioncores) {
                kitten.shrink_to_clausal_core();
                kitten.shuffle_clauses();
                kitten.set_ticks_limit(CORE_TICKS_FACTOR * limit);
                if kitten.solve() == Status::Unknown {
                    cored = false;
                    break;
                }
                let _ = kitten.compute_clausal_core();
            }
            if cored {
                let size0 = self.clauses.watches[widen(lit)].len();
                for id in kitten.core_ids() {
                    let id = widen(id);
                    let (side, word) = if id < size0 {
                        (Side::Positive, self.clauses.watches[widen(lit)][id])
                    } else {
                        (
                            Side::Negative,
                            self.clauses.watches[widen(not_lit)][id - size0],
                        )
                    };
                    self.elimination.gates[side.index()].push(word);
                }
                let [gates0, gates1] = &self.elimination.gates;
                let unit = if gates0.is_empty() {
                    Some(not_lit)
                } else if gates1.is_empty() {
                    Some(lit)
                } else {
                    None
                };
                if let Some(unit) = unit {
                    if self.proof.is_some() {
                        self.trace_one_sided_core_lemmas(unit, &kitten.core_clauses());
                    } else {
                        self.learned_unit(unit);
                    }
                }
                self.elimination.resolve_gate = true;
                res = true;
            }
        }
        self.kitten = Some(kitten);
        res
    }
}
