use std::{fmt::Write as _, io::BufWriter, path::Path, process::Command, time::Duration};

use xsat::{
    options::{Opt, Options},
    proof::{Format, Proof},
    ExternalClause, Gauss, Outcome, Parity, Propagator, Solver,
};

use crate::{
    compare::report,
    config,
    error::DevError,
    process::{self, TempDir},
    random::Random,
};

const USAGE: &str = "xsat-dev assume [--cases N] [--seed N]";
const DEFAULT_CASES: usize = 200;
const VARIABLES: (i64, i64) = (8, 48);
const CLAUSES_PER_HUNDRED_VARIABLES: i64 = 426;
const CLAUSE_SIZE: usize = 3;
const SOLVES: usize = 6;
const MAX_ASSUMPTIONS: i64 = 6;
const MAX_ADDED: i64 = 4;
const NEW_VARIABLES: i32 = 2;
const FROZEN_ONE_IN: i64 = 2;
const PROVED_ONE_IN: u64 = 2;
const PROPAGATED_ONE_IN: u64 = 4;
const HIDDEN_ONE_IN: usize = 4;
const XOR_SEQUENCE: u64 = 3;
const LATE_ONE_IN: u64 = 8;
const LATE_XOR_SEQUENCE: u64 = 7;
const LATE_CALL: usize = 1;
const RESERVE_ONE_IN: i64 = 2;
const PLAIN_SOLVE_ONE_IN: i64 = 2;
const EAGER_ONE_IN: u64 = 2;
const EAGER_SEQUENCE: u64 = 1;
const EAGER_ELIMINATION: i32 = 0;
const XORS: (i64, i64) = (3, 9);
const XOR_SIZE: (i64, i64) = (2, 5);
const KISSAT_DEADLINE: Duration = Duration::from_secs(60);
const SATISFIABLE: i32 = 10;
const UNSATISFIABLE: i32 = 20;

#[derive(Debug)]
struct Hidden {
    clauses: Vec<ExternalClause>,
}

impl Propagator for Hidden {
    fn observed(&self) -> Vec<i32> {
        self.clauses
            .iter()
            .flat_map(ExternalClause::lits)
            .map(|lit| lit.abs())
            .collect()
    }

    fn propagate(&mut self, solver: &Solver) -> Option<ExternalClause> {
        let position = self.clauses.iter().position(|clause| {
            let mut open = 0;
            for &lit in clause.lits() {
                match solver.external_value(lit) {
                    value if value == lit => return false,
                    value if value == -lit => {}
                    _ => open += 1,
                }
            }
            open <= 1
        })?;
        Some(self.clauses.swap_remove(position))
    }
}

struct Formula {
    variables: i32,
    clauses: Vec<Vec<i32>>,
}

fn signed(rng: &mut Random, var: i32) -> i32 {
    if rng.randrange(0, 2) == 0 {
        var
    } else {
        -var
    }
}

fn clause(rng: &mut Random, variables: i32) -> Vec<i32> {
    let mut clause: Vec<i32> = Vec::new();
    while clause.len() < CLAUSE_SIZE {
        let var = i32::try_from(rng.randrange(1, i64::from(variables) + 1)).unwrap_or(1);
        if clause.iter().all(|lit| lit.abs() != var) {
            clause.push(signed(rng, var));
        }
    }
    clause
}

fn formula(rng: &mut Random) -> Formula {
    let variables = i32::try_from(rng.randrange(VARIABLES.0, VARIABLES.1)).unwrap_or(1);
    let count = i64::from(variables) * CLAUSES_PER_HUNDRED_VARIABLES / 100;
    let clauses = (0..count).map(|_| clause(rng, variables)).collect();
    Formula { variables, clauses }
}

fn line(icnf: &mut String, letter: &str, lits: &[i32]) {
    icnf.push_str(letter);
    for lit in lits {
        let _ = write!(icnf, " {lit}");
    }
    icnf.push_str(" 0\n");
}

fn xors(rng: &mut Random, variables: i32) -> Vec<(Vec<i32>, Parity)> {
    (0..rng.randrange(XORS.0, XORS.1))
        .map(|_| {
            let size = usize::try_from(rng.randrange(XOR_SIZE.0, XOR_SIZE.1)).unwrap_or(2);
            let mut lits: Vec<i32> = Vec::new();
            while lits.len() < size.min(usize::try_from(variables).unwrap_or(0)) {
                let var = i32::try_from(rng.randrange(1, i64::from(variables) + 1)).unwrap_or(1);
                if !lits.contains(&var) {
                    lits.push(var);
                }
            }
            let parity = if rng.randrange(0, 2) == 0 {
                Parity::Even
            } else {
                Parity::Odd
            };
            (lits, parity)
        })
        .collect()
}

fn xor_clauses(lits: &[i32], parity: Parity) -> Vec<Vec<i32>> {
    let odd = u32::from(parity == Parity::Odd);
    (0_u32..1 << lits.len())
        .filter(|negated| negated.count_ones() % 2 != odd)
        .map(|negated| {
            lits.iter()
                .enumerate()
                .map(|(bit, &lit)| if negated >> bit & 1 == 1 { -lit } else { lit })
                .collect()
        })
        .collect()
}

fn add(solver: &mut Solver, icnf: &mut String, clause: &[i32]) -> Result<(), DevError> {
    line(icnf, "i", clause);
    for &lit in clause.iter().chain(&[0]) {
        solver.add(lit)?;
    }
    Ok(())
}

fn checked(
    dir: &Path,
    seed: u64,
    icnf: &str,
    solver: &mut Solver,
) -> Result<Option<String>, DevError> {
    let Some(proof) = solver.take_proof() else {
        return Ok(None);
    };
    proof.finish()?;
    let interactions = dir.join(format!("case{seed}.icnf"));
    let trace = dir.join(format!("case{seed}.idrup"));
    std::fs::write(&interactions, icnf)?;
    let ran = process::run(
        Command::new(config::idrup_check())
            .arg("-q")
            .arg(&interactions)
            .arg(&trace),
        KISSAT_DEADLINE,
    )?;
    let verdict = match ran {
        Some(ran) if ran.code == 0 => None,
        Some(ran) => Some(format!(
            "seed {seed}: idrup-check exit {}: {}",
            ran.code,
            String::from_utf8_lossy(&ran.stdout)
                .lines()
                .chain(String::from_utf8_lossy(&ran.stderr).lines())
                .take(3)
                .collect::<Vec<_>>()
                .join(" | ")
        )),
        None => Some(format!("seed {seed}: idrup-check timed out")),
    };
    if verdict.is_none() {
        std::fs::remove_file(&interactions)?;
        std::fs::remove_file(&trace)?;
    }
    Ok(verdict)
}

fn kissat_says(
    kissat: &Path,
    dir: &Path,
    name: &str,
    formula: &Formula,
    units: &[i32],
) -> Result<Option<Outcome>, DevError> {
    let mut dimacs = String::new();
    let _ = writeln!(
        dimacs,
        "p cnf {} {}",
        formula.variables,
        formula.clauses.len() + units.len()
    );
    for clause in formula
        .clauses
        .iter()
        .map(Vec::as_slice)
        .chain(units.chunks(1))
    {
        for lit in clause {
            let _ = write!(dimacs, "{lit} ");
        }
        dimacs.push_str("0\n");
    }
    let path = dir.join(name);
    std::fs::write(&path, dimacs)?;
    let ran = process::run(
        Command::new(kissat).arg("-q").arg("-n").arg(&path),
        KISSAT_DEADLINE,
    )?;
    std::fs::remove_file(&path)?;
    Ok(ran.and_then(|ran| match ran.code {
        SATISFIABLE => Some(Outcome::Satisfiable),
        UNSATISFIABLE => Some(Outcome::Unsatisfiable),
        _ => None,
    }))
}

fn holds(solver: &Solver, lit: i32) -> bool {
    match solver.external_value(lit.abs()) {
        0 => lit > 0,
        value => value == lit,
    }
}

fn session(
    rng: &mut Random,
    dir: &Path,
    seed: u64,
    formula: &mut Formula,
    icnf: &mut String,
) -> Result<Solver, DevError> {
    let mut options = Options::default();
    if seed / PROVED_ONE_IN % EAGER_ONE_IN == EAGER_SEQUENCE {
        options.set(Opt::Eliminateinit, EAGER_ELIMINATION)?;
    }
    let mut solver = Solver::new(options);
    if seed % PROVED_ONE_IN == 0 {
        let trace = std::fs::File::create(dir.join(format!("case{seed}.idrup")))?;
        solver.trace_proof(Proof::new(Box::new(BufWriter::new(trace)), Format::Idrup))?;
    }
    solver.reserve(formula.variables.unsigned_abs())?;
    let hidden = seed % PROPAGATED_ONE_IN == 1;
    let mut propagated = Vec::new();
    for (position, clause) in formula.clauses.iter().enumerate() {
        if hidden && position % HIDDEN_ONE_IN == 0 {
            propagated.push(ExternalClause::new(clause.clone())?);
        } else {
            add(&mut solver, icnf, clause)?;
        }
    }
    if hidden {
        solver.connect(Box::new(Hidden {
            clauses: propagated,
        }))?;
    }
    if seed % PROPAGATED_ONE_IN == XOR_SEQUENCE && seed % LATE_ONE_IN != LATE_XOR_SEQUENCE {
        connect_xors(rng, &mut solver, formula)?;
    }
    for var in 1..=formula.variables {
        if rng.randrange(0, FROZEN_ONE_IN) == 0 {
            solver.freeze(var)?;
        }
    }
    Ok(solver)
}

fn connect_xors(
    rng: &mut Random,
    solver: &mut Solver,
    formula: &mut Formula,
) -> Result<(), DevError> {
    let constraints = xors(rng, formula.variables);
    for (lits, parity) in &constraints {
        formula.clauses.extend(xor_clauses(lits, *parity));
    }
    solver.connect(Box::new(Gauss::new(&constraints)?))?;
    Ok(())
}

fn case(kissat: &Path, dir: &Path, seed: u64) -> Result<Option<String>, DevError> {
    let mut rng = Random::new(seed);
    let mut formula = formula(&mut rng);
    let mut icnf = String::from("p icnf\n");
    let mut solver = session(&mut rng, dir, seed, &mut formula, &mut icnf)?;
    for call in 0..SOLVES {
        if call == LATE_CALL && seed % LATE_ONE_IN == LATE_XOR_SEQUENCE {
            connect_xors(&mut rng, &mut solver, &mut formula)?;
        }
        if call > 0 {
            if rng.randrange(0, RESERVE_ONE_IN) == 0 {
                solver.reserve((formula.variables + NEW_VARIABLES).unsigned_abs())?;
            }
            for _ in 0..rng.randrange(0, MAX_ADDED + 1) {
                let added = clause(&mut rng, formula.variables + NEW_VARIABLES);
                formula.variables = added
                    .iter()
                    .fold(formula.variables, |most, lit| most.max(lit.abs()));
                add(&mut solver, &mut icnf, &added)?;
                formula.clauses.push(added);
            }
        }
        let mut assumptions = Vec::new();
        for _ in 0..rng.randrange(0, MAX_ASSUMPTIONS + 1) {
            let var =
                i32::try_from(rng.randrange(1, i64::from(formula.variables) + 1)).unwrap_or(1);
            assumptions.push(signed(&mut rng, var));
        }
        let fail = |what: &str| {
            Some(format!(
                "seed {seed} call {call} assuming {assumptions:?}: {what}"
            ))
        };
        line(&mut icnf, "q", &assumptions);
        let outcome = if assumptions.is_empty() && rng.randrange(0, PLAIN_SOLVE_ONE_IN) == 0 {
            solver.solve()?
        } else {
            solver.solve_assuming(&assumptions)?
        };
        icnf.push_str(match outcome {
            Outcome::Satisfiable => "s SATISFIABLE\n",
            Outcome::Unsatisfiable => "s UNSATISFIABLE\n",
            Outcome::Unknown => "s UNKNOWN\n",
        });
        match outcome {
            Outcome::Satisfiable => {
                let model: Vec<i32> = (1..=formula.variables)
                    .map(|var| if holds(&solver, var) { var } else { -var })
                    .collect();
                line(&mut icnf, "m", &model);
            }
            Outcome::Unsatisfiable => line(&mut icnf, "u", solver.core()),
            Outcome::Unknown => {}
        }
        let name = format!("case{seed}.cnf");
        let expected = kissat_says(kissat, dir, &name, &formula, &assumptions)?;
        if expected != Some(outcome) {
            return Ok(fail(&format!("xsat {outcome:?}, kissat {expected:?}")));
        }
        match outcome {
            Outcome::Satisfiable => {
                let model = formula
                    .clauses
                    .iter()
                    .all(|clause| clause.iter().any(|&lit| holds(&solver, lit)))
                    && assumptions.iter().all(|&lit| holds(&solver, lit));
                if !model {
                    return Ok(fail("model falsifies a clause or an assumption"));
                }
            }
            Outcome::Unsatisfiable => {
                let core = solver.core().to_vec();
                if !core.iter().all(|lit| assumptions.contains(lit)) {
                    return Ok(fail(&format!("core {core:?} is not a subset")));
                }
                let refuted = kissat_says(kissat, dir, &name, &formula, &core)?;
                if refuted != Some(Outcome::Unsatisfiable) {
                    return Ok(fail(&format!("core {core:?} is satisfiable")));
                }
            }
            Outcome::Unknown => return Ok(fail("unknown without a limit")),
        }
    }
    checked(dir, seed, &icnf, &mut solver)
}

pub(crate) fn assume(kissat: &Path, args: &[String]) -> Result<bool, DevError> {
    let (mut count, mut seed) = (DEFAULT_CASES, 0_u64);
    let mut args = args.iter();
    while let Some(arg) = args.next() {
        let value = args.next().and_then(|value| value.parse().ok());
        match (arg.as_str(), value) {
            ("--cases", Some(value)) => count = usize::try_from(value).unwrap_or(count),
            ("--seed", Some(value)) => seed = value,
            _ => return Err(DevError::Usage(USAGE)),
        }
    }
    let dir = TempDir::new("xsat-assume")?;
    let seeds: Vec<u64> = (0..count)
        .filter_map(|at| u64::try_from(at).ok())
        .map(|at| seed.wrapping_add(at))
        .collect();
    let differences: Vec<String> = process::parallel(&seeds, config::jobs(), |&seed| {
        case(kissat, dir.path(), seed)
    })?
    .into_iter()
    .filter_map(Result::transpose)
    .collect::<Result<_, _>>()?;
    Ok(report(
        &differences,
        count,
        "solve sequences agree with kissat",
    ))
}
