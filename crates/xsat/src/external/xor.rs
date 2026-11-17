use crate::{
    error::SolverError,
    external::propagator::{ExternalClause, Propagator},
    solver::{checked_literal, Solver},
};

const WORD: usize = 64;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Parity {
    Even,
    Odd,
}

#[derive(Clone, PartialEq, Eq, Debug)]
struct Row {
    bits: Vec<u64>,
    odd: bool,
}

impl Row {
    fn has(&self, column: usize) -> bool {
        self.bits[column / WORD] >> (column % WORD) & 1 == 1
    }

    fn flip(&mut self, column: usize) {
        self.bits[column / WORD] ^= 1 << (column % WORD);
    }

    fn add(&mut self, other: &Row) {
        for (word, &other) in self.bits.iter_mut().zip(&other.bits) {
            *word ^= other;
        }
        self.odd ^= other.odd;
    }
}

#[derive(Debug)]
pub struct Gauss {
    variables: Vec<i32>,
    rows: Vec<Row>,
}

impl Gauss {
    pub fn new(constraints: &[(Vec<i32>, Parity)]) -> Result<Gauss, SolverError> {
        for &lit in constraints.iter().flat_map(|(lits, _)| lits) {
            checked_literal(lit)?;
        }
        let mut variables: Vec<i32> = constraints
            .iter()
            .flat_map(|(lits, _)| lits.iter().map(|lit| lit.abs()))
            .collect();
        variables.sort_unstable();
        variables.dedup();
        let words = variables.len().div_ceil(WORD);
        let rows = constraints
            .iter()
            .map(|(lits, parity)| {
                let mut row = Row {
                    bits: vec![0; words],
                    odd: *parity == Parity::Odd,
                };
                for &lit in lits {
                    if let Ok(column) = variables.binary_search(&lit.abs()) {
                        row.flip(column);
                    }
                    if lit < 0 {
                        row.odd = !row.odd;
                    }
                }
                row
            })
            .collect();
        Ok(Gauss { variables, rows })
    }
}

impl Propagator for Gauss {
    fn observed(&self) -> Vec<i32> {
        self.variables.clone()
    }

    fn propagate(&mut self, solver: &Solver) -> Option<ExternalClause> {
        let values: Vec<i32> = self
            .variables
            .iter()
            .map(|&var| solver.external_value(var).signum())
            .collect();
        let mut rows = self.rows.clone();
        let mut rank = 0;
        for column in (0..self.variables.len()).filter(|&column| values[column] == 0) {
            let Some(found) = (rank..rows.len()).find(|&row| rows[row].has(column)) else {
                continue;
            };
            rows.swap(rank, found);
            let pivot = rows[rank].clone();
            for (row, other) in rows.iter_mut().enumerate() {
                if row != rank && other.has(column) {
                    other.add(&pivot);
                }
            }
            rank += 1;
        }
        rows.iter().find_map(|row| self.implied(row, &values))
    }
}

impl Gauss {
    fn implied(&self, row: &Row, values: &[i32]) -> Option<ExternalClause> {
        let mut odd = row.odd;
        let mut open = None;
        let mut clause = Vec::new();
        for (column, &var) in self.variables.iter().enumerate() {
            if !row.has(column) {
                continue;
            }
            match values[column] {
                0 if open.is_some() => return None,
                0 => open = Some(var),
                value => {
                    odd ^= value > 0;
                    clause.push(-value * var);
                }
            }
        }
        match open {
            Some(var) => clause.insert(0, if odd { var } else { -var }),
            None if !odd => return None,
            None => {}
        }
        Some(ExternalClause::from_checked(clause))
    }
}
