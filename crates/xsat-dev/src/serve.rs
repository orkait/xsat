use std::{
    collections::BTreeSet,
    io::{self, BufRead as _, BufReader, Write as _},
    path::Path,
    process::{Child, ChildStdin, ChildStdout, Command, Stdio},
};

use crate::{compare::sampled, error::DevError, random::Random};

const DEFAULT_CASES: usize = 400;
const VARIABLES: (i32, i32) = (3, 13);
const CLAUSES_PER_VARIABLE: i32 = 4;
const CLAUSE_SIZE: usize = 3;
const STEPS: usize = 10;
const BATCH: (i32, i32) = (1, 6);
const MAX_ASSUMPTIONS: i32 = 4;
const LIMITS: [u64; 5] = [0, 0, 1, 2, 3];
const SERVE: &str = "--serve";
const ADD: &str = "a";
const SOLVE: &str = "s";
const MODEL: &str = "m";
const CORE: &str = "u";
const ENUMERATE: &str = "e";
const VALUES: &str = "v";
const REFUSED: &str = "x ";
const SATISFIABLE: &str = "s SATISFIABLE";
const UNSATISFIABLE: &str = "s UNSATISFIABLE";
const MALFORMED: [&str; 4] = ["q 1 0", "s 1", "a 1 x 0", "s 1 0 2 0"];
const END: i32 = 0;

#[derive(Clone, Copy)]
enum Step {
    Add,
    Solve,
    Enumerate,
    Refuse,
}

struct Server {
    child: Child,
    input: ChildStdin,
    output: BufReader<ChildStdout>,
}

impl Server {
    fn start(xsat: &Path) -> io::Result<Server> {
        let mut child = Command::new(xsat)
            .arg(SERVE)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::null())
            .spawn()?;
        let (Some(input), Some(output)) = (child.stdin.take(), child.stdout.take()) else {
            return Err(io::Error::other("xsat --serve without pipes"));
        };
        Ok(Server {
            child,
            input,
            output: BufReader::new(output),
        })
    }

    fn ask(&mut self, kind: &str, lits: impl IntoIterator<Item = i32>) -> io::Result<()> {
        let mut words = vec![kind.to_owned()];
        words.extend(lits.into_iter().map(|lit| lit.to_string()));
        writeln!(self.input, "{}", words.join(" "))?;
        self.input.flush()
    }

    fn reply(&mut self) -> io::Result<String> {
        let mut line = String::new();
        self.output.read_line(&mut line)?;
        Ok(line.trim_end().to_owned())
    }

    fn finish(mut self) -> io::Result<bool> {
        drop(self.input);
        Ok(self.child.wait()?.success())
    }
}

fn draw(rng: &mut Random, (start, stop): (i32, i32)) -> i32 {
    i32::try_from(rng.randrange(start.into(), stop.into())).unwrap_or(start)
}

fn literal(rng: &mut Random, variables: i32) -> i32 {
    let variable = draw(rng, (1, variables + 1));
    rng.pick([variable, -variable])
}

fn clause(rng: &mut Random, variables: i32) -> Vec<i32> {
    (0..CLAUSE_SIZE).map(|_| literal(rng, variables)).collect()
}

fn holds(assignment: u32, lit: i32) -> bool {
    (assignment >> (lit.unsigned_abs() - 1) & 1 == 1) == (lit > 0)
}

fn satisfies(assignment: u32, clauses: &[Vec<i32>], assumptions: &[i32]) -> bool {
    assumptions.iter().all(|&lit| holds(assignment, lit))
        && clauses
            .iter()
            .all(|clause| clause.iter().any(|&lit| holds(assignment, lit)))
}

fn assignments(variables: i32) -> std::ops::Range<u32> {
    0..1_u32 << variables
}

fn satisfiable(variables: i32, clauses: &[Vec<i32>], assumptions: &[i32]) -> bool {
    assignments(variables).any(|assignment| satisfies(assignment, clauses, assumptions))
}

fn project(assignment: u32, projection: &[i32]) -> Vec<i32> {
    projection
        .iter()
        .map(|&variable| {
            if holds(assignment, variable) {
                variable
            } else {
                -variable
            }
        })
        .collect()
}

fn listed(reply: &str, prefix: &str) -> Option<Vec<i32>> {
    let mut lits = reply
        .strip_prefix(prefix)?
        .split_ascii_whitespace()
        .map(|token| token.parse().ok())
        .collect::<Option<Vec<i32>>>()?;
    (lits.pop() == Some(END)).then_some(lits)
}

fn assignment_of(model: &[i32], variables: i32) -> Option<u32> {
    if model.len() != usize::try_from(variables).ok()? {
        return None;
    }
    (1..=variables)
        .zip(model)
        .try_fold(0, |assignment, (variable, &lit)| match lit {
            lit if lit == variable => Some(assignment | 1 << (variable - 1)),
            lit if lit == -variable => Some(assignment),
            _ => None,
        })
}

struct Case {
    rng: Random,
    variables: i32,
    clauses: Vec<Vec<i32>>,
    server: Server,
}

impl Case {
    fn add(&mut self) -> io::Result<Option<String>> {
        let batch: Vec<Vec<i32>> = (0..draw(&mut self.rng, BATCH))
            .map(|_| clause(&mut self.rng, self.variables))
            .collect();
        self.send(&batch)?;
        self.clauses.extend(batch);
        Ok(None)
    }

    fn send(&mut self, clauses: &[Vec<i32>]) -> io::Result<()> {
        if clauses.is_empty() {
            return Ok(());
        }
        self.server.ask(
            ADD,
            clauses
                .iter()
                .flat_map(|clause| clause.iter().copied().chain([END])),
        )
    }

    fn solve(&mut self) -> io::Result<Option<String>> {
        let assumptions: Vec<i32> = (0..draw(&mut self.rng, (0, MAX_ASSUMPTIONS + 1)))
            .map(|_| literal(&mut self.rng, self.variables))
            .collect();
        let want = if satisfiable(self.variables, &self.clauses, &assumptions) {
            SATISFIABLE
        } else {
            UNSATISFIABLE
        };
        self.server
            .ask(SOLVE, assumptions.iter().copied().chain([END]))?;
        let status = self.server.reply()?;
        if status != want {
            return Ok(Some(format!(
                "solve under {assumptions:?} answered '{status}', expected '{want}'"
            )));
        }
        if want == SATISFIABLE {
            self.server.ask(MODEL, (1..=self.variables).chain([END]))?;
            let reply = self.server.reply()?;
            let model =
                listed(&reply, VALUES).and_then(|model| assignment_of(&model, self.variables));
            if !model.is_some_and(|model| satisfies(model, &self.clauses, &assumptions)) {
                return Ok(Some(format!(
                    "model '{reply}' under {assumptions:?} is wrong"
                )));
            }
        } else if !assumptions.is_empty() {
            self.server.ask(CORE, [])?;
            let reply = self.server.reply()?;
            let core = listed(&reply, CORE).filter(|core| {
                core.iter().all(|lit| assumptions.contains(lit))
                    && !satisfiable(self.variables, &self.clauses, core)
            });
            if core.is_none() {
                return Ok(Some(format!(
                    "core '{reply}' under {assumptions:?} is wrong"
                )));
            }
        }
        Ok(None)
    }

    fn enumerate(&mut self) -> io::Result<Option<String>> {
        let mut projection: Vec<i32> = (1..=self.variables)
            .filter(|_| self.rng.pick([true, false]))
            .collect();
        if projection.is_empty() {
            projection.push(1);
        }
        let limit = self.rng.pick(LIMITS);
        let models: BTreeSet<Vec<i32>> = assignments(self.variables)
            .filter(|&assignment| satisfies(assignment, &self.clauses, &[]))
            .map(|assignment| project(assignment, &projection))
            .collect();
        self.server.ask(
            &format!("{ENUMERATE} {limit}"),
            projection.iter().copied().chain([END]),
        )?;
        let mut seen = BTreeSet::new();
        let status = loop {
            let reply = self.server.reply()?;
            let Some(model) = listed(&reply, VALUES) else {
                break reply;
            };
            if !models.contains(&model) || !seen.insert(model.clone()) {
                return Ok(Some(format!(
                    "enumerated model '{reply}' is wrong or repeated"
                )));
            }
            self.clauses.push(model.iter().map(|lit| -lit).collect());
        };
        let stopped = limit != 0 && u64::try_from(seen.len()) == Ok(limit);
        let complete = seen.len() == models.len();
        let want = if stopped { SATISFIABLE } else { UNSATISFIABLE };
        if status != want || (!stopped && !complete) {
            return Ok(Some(format!(
                "enumeration with limit {limit} gave {} of {} models and '{status}'",
                seen.len(),
                models.len()
            )));
        }
        Ok(None)
    }

    fn refuse(&mut self) -> io::Result<Option<String>> {
        let request = self.rng.pick(MALFORMED);
        writeln!(self.server.input, "{request}")?;
        self.server.input.flush()?;
        let reply = self.server.reply()?;
        Ok((!reply.starts_with(REFUSED))
            .then(|| format!("malformed '{request}' answered '{reply}'")))
    }
}

fn case(xsat: &Path, seed: u64) -> Result<Option<String>, DevError> {
    let mut rng = Random::new(seed);
    let variables = draw(&mut rng, VARIABLES);
    let clauses: Vec<Vec<i32>> = (0..draw(&mut rng, (0, variables * CLAUSES_PER_VARIABLE)))
        .map(|_| clause(&mut rng, variables))
        .collect();
    let mut case = Case {
        rng,
        variables,
        clauses: Vec::new(),
        server: Server::start(xsat)?,
    };
    case.send(&clauses)?;
    case.clauses = clauses;
    for step in 0..STEPS {
        let fault = match case.rng.pick([
            Step::Add,
            Step::Solve,
            Step::Solve,
            Step::Enumerate,
            Step::Refuse,
        ]) {
            Step::Add => case.add(),
            Step::Solve => case.solve(),
            Step::Enumerate => case.enumerate(),
            Step::Refuse => case.refuse(),
        }?;
        if let Some(fault) = fault {
            return Ok(Some(format!("seed {seed} step {step}: {fault}")));
        }
    }
    Ok((!case.server.finish()?).then(|| format!("seed {seed}: xsat --serve failed")))
}

pub(crate) fn check(xsat: &Path, args: &[String]) -> Result<bool, DevError> {
    sampled(
        args,
        DEFAULT_CASES,
        "serve sessions agree with brute force",
        |seed| case(xsat, seed),
    )
}
