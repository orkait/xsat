use std::io::{self, BufRead as _, Write};

use thiserror::Error;
use xsat::{dimacs::MAX_VARIABLE, error::SolverError, options::Options, Outcome, Solver};

use crate::{printed_value, Failure, SATISFIABLE, UNKNOWN, UNSATISFIABLE};

const ADD: &str = "a";
const SOLVE: &str = "s";
const MODEL: &str = "m";
const CORE: &str = "u";
const ENUMERATE: &str = "e";
const LIMIT: &str = "l";
const REFUSED: &str = "x";
const VALUES: &str = "v";
const END: i32 = 0;
const UNLIMITED: u64 = 0;

#[derive(Debug, Error)]
enum RequestError {
    #[error("empty request")]
    Empty,
    #[error("unknown request '{0}'")]
    Unknown(String),
    #[error("'{0}' is not a literal")]
    Literal(String),
    #[error("'{0}' is not a count")]
    Count(String),
    #[error("missing count")]
    MissingCount,
    #[error("literals must end in 0")]
    Unterminated,
    #[error("0 inside a literal list")]
    InnerZero,
    #[error("no model: the last solve was not satisfiable")]
    NoModel,
    #[error(transparent)]
    Solver(#[from] SolverError),
    #[error(transparent)]
    Output(#[from] io::Error),
}

struct Session {
    solver: Solver,
    variables: i32,
    model: bool,
}

pub(crate) fn serve(options: Options, out: &mut impl Write) -> Result<(), Failure> {
    let mut session = Session {
        solver: Solver::new(options),
        variables: 0,
        model: false,
    };
    let mut input = io::stdin().lock();
    let mut line = String::new();
    loop {
        line.clear();
        if input.read_line(&mut line)? == 0 {
            return Ok(());
        }
        match session.answer(&line, out) {
            Ok(()) => {}
            Err(RequestError::Solver(error)) => return Err(error.into()),
            Err(RequestError::Output(error)) => return Err(error.into()),
            Err(refusal) => writeln!(out, "{REFUSED} {refusal}")?,
        }
        out.flush()?;
    }
}

fn literal(token: &str) -> Result<i32, RequestError> {
    token
        .parse::<i32>()
        .ok()
        .filter(|lit| lit.unsigned_abs() <= MAX_VARIABLE.unsigned_abs())
        .ok_or_else(|| RequestError::Literal(token.to_owned()))
}

fn clauses<'a>(tokens: impl Iterator<Item = &'a str>) -> Result<Vec<i32>, RequestError> {
    let lits = tokens.map(literal).collect::<Result<Vec<_>, _>>()?;
    if lits.last() == Some(&END) {
        Ok(lits)
    } else {
        Err(RequestError::Unterminated)
    }
}

fn list<'a>(tokens: impl Iterator<Item = &'a str>) -> Result<Vec<i32>, RequestError> {
    let mut lits = clauses(tokens)?;
    lits.pop();
    if lits.contains(&END) {
        return Err(RequestError::InnerZero);
    }
    Ok(lits)
}

fn count(token: Option<&str>) -> Result<u64, RequestError> {
    let token = token.ok_or(RequestError::MissingCount)?;
    token
        .parse()
        .map_err(|_| RequestError::Count(token.to_owned()))
}

fn status(outcome: Outcome) -> &'static str {
    match outcome {
        Outcome::Satisfiable => SATISFIABLE,
        Outcome::Unsatisfiable => UNSATISFIABLE,
        Outcome::Unknown => UNKNOWN,
    }
}

fn write_lits(out: &mut impl Write, prefix: &str, lits: &[i32]) -> io::Result<()> {
    write!(out, "{prefix}")?;
    for lit in lits {
        write!(out, " {lit}")?;
    }
    writeln!(out, " {END}")
}

impl Session {
    fn answer(&mut self, line: &str, out: &mut impl Write) -> Result<(), RequestError> {
        let mut tokens = line.split_ascii_whitespace();
        match tokens.next().ok_or(RequestError::Empty)? {
            ADD => {
                let lits = clauses(tokens)?;
                self.model = false;
                for lit in lits {
                    self.claim(lit);
                    self.solver.add(lit)?;
                }
            }
            SOLVE => {
                let assumptions = list(tokens)?;
                for &lit in &assumptions {
                    self.claim(lit);
                }
                let outcome = self.solver.solve_assuming(&assumptions)?;
                self.model = outcome == Outcome::Satisfiable;
                writeln!(out, "{}", status(outcome))?;
            }
            MODEL => {
                let projection = self.projection(&list(tokens)?);
                if !self.model {
                    return Err(RequestError::NoModel);
                }
                write_lits(out, VALUES, &self.values(&projection))?;
            }
            CORE => write_lits(out, CORE, self.solver.core())?,
            ENUMERATE => {
                let limit = count(tokens.next())?;
                let projection = self.projection(&list(tokens)?);
                self.enumerate(limit, &projection, out)?;
            }
            LIMIT => self.solver.limit_conflicts(count(tokens.next())?),
            other => return Err(RequestError::Unknown(other.to_owned())),
        }
        Ok(())
    }

    fn claim(&mut self, lit: i32) {
        self.variables = self.variables.max(lit.abs());
    }

    fn projection(&self, variables: &[i32]) -> Vec<i32> {
        if variables.is_empty() {
            (1..=self.variables).collect()
        } else {
            variables.iter().map(|variable| variable.abs()).collect()
        }
    }

    fn values(&self, projection: &[i32]) -> Vec<i32> {
        projection
            .iter()
            .map(|&variable| printed_value(&self.solver, variable))
            .collect()
    }

    fn enumerate(
        &mut self,
        limit: u64,
        projection: &[i32],
        out: &mut impl Write,
    ) -> Result<(), RequestError> {
        let mut models = 0;
        let outcome = loop {
            if limit != UNLIMITED && models == limit {
                break Outcome::Satisfiable;
            }
            let outcome = self.solver.solve()?;
            if outcome != Outcome::Satisfiable {
                break outcome;
            }
            models += 1;
            let model = self.values(projection);
            write_lits(out, VALUES, &model)?;
            for lit in model {
                self.solver.add(-lit)?;
            }
            self.solver.add(END)?;
        };
        self.model = false;
        writeln!(out, "{}", status(outcome))?;
        Ok(())
    }
}
