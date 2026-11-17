use crate::{
    dimacs::MAX_VARIABLE,
    solver::{idx, negated, Solver},
    store::{arena::Ref, convert::widen},
    trace::proof::Step,
};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Label {
    Witness,
    Clause,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) struct Extension {
    lit: i32,
    label: Label,
}

impl Solver {
    pub(crate) fn export_literal(&self, ilit: u32) -> i32 {
        let elit = i32::try_from(self.exports[widen(idx(ilit))]).unwrap_or(0);
        if negated(ilit) {
            -elit
        } else {
            elit
        }
    }

    fn push_witness_literal(&mut self, ilit: u32) {
        let lit = self.export_literal(ilit);
        self.extend.push(Extension {
            lit,
            label: Label::Witness,
        });
    }

    fn push_clause_literal(&mut self, ilit: u32) {
        let lit = self.export_literal(ilit);
        self.extend.push(Extension {
            lit,
            label: Label::Clause,
        });
    }

    pub(crate) fn weaken_clause(&mut self, lit: u32, at: Ref) {
        self.push_witness_literal(lit);
        for position in 0..self.clauses.arena.size(at) {
            let other = self.clauses.arena.lit(at, position);
            if other != lit {
                self.push_clause_literal(other);
            }
        }
    }

    pub(crate) fn weaken_binary(&mut self, lit: u32, other: u32) {
        self.push_witness_literal(lit);
        self.push_clause_literal(other);
    }

    #[expect(
        clippy::expect_used,
        reason = "external indices are bounded by MAX_VARIABLE as in Kissat; running out is a resource limit"
    )]
    pub(crate) fn claim_variable(&mut self, elit: i32) {
        let eidx = elit.unsigned_abs();
        if !self.extension.get(widen(eidx)).copied().unwrap_or(false) {
            return;
        }
        let moved_lit = i32::try_from(self.imports.len())
            .ok()
            .filter(|&lit| lit <= MAX_VARIABLE)
            .expect("maximum variable index exhausted");
        let moved = moved_lit.unsigned_abs();
        let relocate = |lit: &mut i32| {
            if lit.unsigned_abs() == eidx {
                *lit = if *lit < 0 { -moved_lit } else { moved_lit };
            }
        };
        self.extension[widen(eidx)] = false;
        self.extension.resize(widen(moved) + 1, false);
        self.extension[widen(moved)] = true;
        let imported = self.imports[widen(eidx)].take();
        self.imports.push(imported);
        if let Some(ilit) = imported {
            let export = &mut self.exports[widen(idx(ilit))];
            if *export == eidx {
                *export = moved;
            }
        }
        if let Some(slot) = self
            .eliminated_at
            .get_mut(widen(eidx))
            .and_then(Option::take)
        {
            self.eliminated_at.resize(widen(moved) + 1, None);
            self.eliminated_at[widen(moved)] = Some(slot);
        }
        for extension in &mut self.extend {
            relocate(&mut extension.lit);
        }
        self.units.iter_mut().for_each(relocate);
    }

    pub(crate) fn restore_clauses(&mut self) {
        while let Some(eidx) = self.restoring.pop() {
            let mut restored = Vec::new();
            let mut kept = Vec::with_capacity(self.extend.len());
            for group in self.extend.chunk_by(|_, next| next.label == Label::Clause) {
                if group[0].lit.unsigned_abs() == eidx {
                    restored.push(
                        group
                            .iter()
                            .map(|extension| extension.lit)
                            .collect::<Vec<_>>(),
                    );
                } else {
                    kept.extend_from_slice(group);
                }
            }
            self.extend = kept;
            for clause in restored {
                self.proof_external(Step::Restore, &clause);
                for elit in clause {
                    self.add_literal(elit);
                }
                self.add_literal(0);
            }
        }
    }

    pub(crate) fn eliminated_slot(&self, elit: i32) -> Option<u32> {
        self.eliminated_at
            .get(widen(elit.unsigned_abs()))
            .copied()
            .flatten()
    }

    fn extend_assign(&mut self, elit: i32) {
        if let Some(at) = self.eliminated_slot(elit) {
            self.eliminated[widen(at)] = if elit < 0 { -1 } else { 1 };
        }
    }

    pub(crate) fn extend(&mut self) {
        let mut end = self.extend.len();
        while end > 0 {
            let mut satisfied = false;
            let mut eliminated: Option<(i32, u32)> = None;
            let witness = loop {
                end -= 1;
                let extension = self.extend[end];
                let elit = extension.lit;
                if !satisfied {
                    let value = self.external_variable_value(elit.unsigned_abs());
                    if let Some(at) = self.eliminated_slot(elit) {
                        if value == 0 && eliminated.is_none_or(|(_, pos)| pos < at) {
                            eliminated = Some((elit, at));
                        }
                    }
                    satisfied = if elit < 0 { value < 0 } else { value > 0 };
                }
                if extension.label == Label::Witness {
                    break elit;
                }
            };
            if satisfied {
                continue;
            }
            match eliminated {
                Some((elit, _)) if elit != witness => self.extend_assign(elit),
                _ => self.extend_assign(witness),
            }
        }
    }
}
