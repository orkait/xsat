use std::{
    fs::File,
    io::{self, BufWriter, ErrorKind, Read, Write},
    path::PathBuf,
    process::{Child, Command, ExitCode, Stdio},
    time::Duration,
};

use thiserror::Error;
use xsat::{
    dimacs::{Dimacs, Strictness},
    error::SolverError,
    options::{parse_arg, parse_value, Configuration, Opt, Options, SPECS},
    parallel::Portfolio,
    proof::{Format, Proof},
    statistics::Verbosity,
    unported, Outcome, Solver, KISSAT_VERSION,
};

#[global_allocator]
static ALLOCATOR: mimalloc::MiMalloc = mimalloc::MiMalloc;

const USAGE: &str = "usage: xsat [ <option> ... ] [ <dimacs> [ <proof> ] ]";
const STDOUT: &str = "-";
const FORCE: [&str; 5] = ["-f", "--force", "--force=1", "--force=true", "--forced"];
const NO_BINARY: [&str; 3] = ["--no-binary", "--binary=0", "--binary=false"];
const NO_WITNESS: &str = "-n";
const STATISTICS_SHORT: &str = "-s";
const CNF_SUFFIXES: [&str; 2] = [".cnf", ".dimacs"];
const COMPRESSED_SUFFIXES: [&str; 6] = ["", ".7z", ".bz2", ".gz", ".lzma", ".xz"];
const NAME_WIDTH: usize = 30;
const VALUE_WIDTH: usize = 12;
const STDIN: &str = "<stdin>";
const UNKNOWN: &str = "s UNKNOWN";
const LONG: &str = "--";
const CONFLICTS: &str = "--conflicts=";
const DECISIONS: &str = "--decisions=";
const TIME: &str = "--time=";
const LEAST_COUNT: u64 = 0;
const LEAST_SECONDS: u64 = 1;
const LIMITS: [&str; 3] = [
    "--conflicts=<limit>",
    "--decisions=<limit>",
    "--time=<seconds>",
];
const WORKERS: &str = "--workers=";
const SHORT: char = '-';
const QUIET_SHORT: &str = "-q";
const OFF: i32 = 0;
const ON: i32 = 1;
const EXIT_UNKNOWN: u8 = 0;
const EXIT_SATISFIABLE: u8 = 10;
const EXIT_UNSATISFIABLE: u8 = 20;
const WITNESS_WIDTH: usize = 77;
const EXIT_ERROR: u8 = 1;
const EXIT_BROKEN_PIPE: u8 = 141;
const RELAXED: [&str; 2] = ["--relax", "--relaxed"];
const PEDANTIC: [&str; 3] = ["--strict", "--stricter", "--pedantic"];

struct Decompressor {
    suffix: &'static str,
    program: &'static str,
    args: &'static [&'static str],
    signature: &'static [u8],
}

const DECOMPRESSORS: [Decompressor; 6] = [
    Decompressor {
        suffix: ".bz2",
        program: "bzip2",
        args: &["-c", "-d"],
        signature: &[0x42, 0x5A, 0x68],
    },
    Decompressor {
        suffix: ".gz",
        program: "gzip",
        args: &["-c", "-d"],
        signature: &[0x1F, 0x8B],
    },
    Decompressor {
        suffix: ".lzma",
        program: "lzma",
        args: &["-c", "-d"],
        signature: &[0x5D, 0x00, 0x00, 0x80, 0x00],
    },
    Decompressor {
        suffix: ".7z",
        program: "7z",
        args: &["x", "-so"],
        signature: &[0x37, 0x7A, 0xBC, 0xAF, 0x27, 0x1C],
    },
    Decompressor {
        suffix: ".xz",
        program: "xz",
        args: &["-c", "-d"],
        signature: &[0xFD, 0x37, 0x7A, 0x58, 0x5A, 0x00, 0x00],
    },
    Decompressor {
        suffix: ".Z",
        program: "gzip",
        args: &["-c", "-d"],
        signature: &[0x1F, 0x9D, 0x90],
    },
];

enum Action {
    Solve(Box<Run>),
    Range,
    Help,
    Version,
}

struct Run {
    options: Options,
    strictness: Strictness,
    path: Option<String>,
    proof: Option<String>,
    format: Format,
    force: bool,
    witness: bool,
    conflicts: Option<u64>,
    decisions: Option<u64>,
    time: Option<u64>,
    workers: usize,
}

struct Source {
    reader: Box<dyn Read>,
    child: Option<Child>,
}

fn invocation(args: &[String]) -> Result<Action, String> {
    let mut run = Run {
        options: Options::default(),
        strictness: Strictness::Normal,
        path: None,
        proof: None,
        format: Format::Binary,
        force: false,
        witness: true,
        conflicts: None,
        decisions: None,
        time: None,
        workers: 1,
    };
    let mut strict_option: Option<&str> = None;
    let mut configuration: Option<&str> = None;
    let mut conflicts_option: Option<&str> = None;
    let mut decisions_option: Option<&str> = None;
    let mut time_option: Option<&str> = None;
    for arg in args {
        let arg = arg.as_str();
        let strictness = if RELAXED.contains(&arg) {
            Some(Strictness::Relaxed)
        } else if PEDANTIC.contains(&arg) {
            Some(Strictness::Pedantic)
        } else {
            None
        };
        if let Some(strictness) = strictness {
            if let Some(previous) = strict_option {
                return Err(if run.strictness != strictness {
                    format!("can not combine contradictory '{previous}' and '{arg}'")
                } else if previous == arg {
                    format!("multiple '{previous}' options")
                } else {
                    format!("'{previous}' and '{arg}' have the same effect")
                });
            }
            run.strictness = strictness;
            strict_option = Some(arg);
            continue;
        }
        match arg {
            "-h" | "--help" => return Ok(Action::Help),
            "--range" => return Ok(Action::Range),
            "--version" => return Ok(Action::Version),
            QUIET_SHORT => {
                run.options
                    .set(Opt::Quiet, ON)
                    .map_err(|error| error.to_string())?;
                continue;
            }
            STATISTICS_SHORT => {
                run.options
                    .set(Opt::Statistics, ON)
                    .map_err(|error| error.to_string())?;
                continue;
            }
            NO_WITNESS => {
                run.witness = false;
                continue;
            }
            _ => {}
        }
        if FORCE.contains(&arg) {
            run.force = true;
            continue;
        }
        if NO_BINARY.contains(&arg) {
            run.format = Format::Ascii;
            continue;
        }
        if let Some(value) = arg.strip_prefix(WORKERS) {
            run.workers = workers(arg, value)?;
            continue;
        }
        if let Some(value) = arg.strip_prefix(CONFLICTS) {
            run.conflicts = Some(limit(arg, value, &mut conflicts_option, LEAST_COUNT)?);
        } else if let Some(value) = arg.strip_prefix(DECISIONS) {
            run.decisions = Some(limit(arg, value, &mut decisions_option, LEAST_COUNT)?);
        } else if let Some(value) = arg.strip_prefix(TIME) {
            run.time = Some(limit(arg, value, &mut time_option, LEAST_SECONDS)?);
        } else if let Some(found) = arg.strip_prefix(LONG).and_then(Configuration::named) {
            if let Some(previous) = configuration {
                return Err(format!("multiple configurations '{previous}' and '{arg}'"));
            }
            run.options.configure(found);
            configuration = Some(arg);
        } else if arg.starts_with(LONG) {
            let invalid = || format!("invalid long option '{arg}' (try '-h')");
            let (opt, value) = parse_arg(arg).ok_or_else(invalid)?;
            run.options.set(opt, value).map_err(|_| invalid())?;
        } else if arg.len() > 1 && arg.starts_with(SHORT) {
            return Err(format!("invalid short option '{arg}' (try '-h')"));
        } else {
            file_argument(&mut run, arg)?;
        }
    }
    Ok(Action::Solve(Box::new(run)))
}

fn same_file(input: &str, proof: &str) -> Option<PathBuf> {
    let real = std::fs::canonicalize(input).ok()?;
    (std::fs::canonicalize(proof).ok()? == real).then_some(real)
}

fn file_argument(run: &mut Run, arg: &str) -> Result<(), String> {
    if let (Some(input), Some(proof)) = (&run.path, &run.proof) {
        return Err(format!(
            "three file arguments '{input}', '{proof}' and '{arg}' (try '-h')"
        ));
    }
    if let Some(input) = &run.path {
        if input == arg {
            return Err(format!(
                "will not read and write '{input}' at the same time"
            ));
        }
        if let Some(real) = same_file(input, arg) {
            let real = real.display().to_string();
            return Err(if arg != real && *input != real {
                format!(
                    "will not read and write '{input}' and '{arg}' pointing to the same file '{real}'"
                )
            } else {
                format!("will not read and write '{input}' and '{arg}' pointing to the same file")
            });
        }
        if !run.force && most_likely_existing_cnf_file(arg) {
            return Err(format!("not writing proof to '{arg}' file (use '-f')"));
        }
        run.proof = Some(arg.to_owned());
    } else if File::open(arg).is_err() {
        return Err(format!("can not read '{arg}'"));
    } else {
        run.path = Some(arg.to_owned());
    }
    Ok(())
}

fn open(path: Option<&str>) -> io::Result<Source> {
    let Some(path) = path else {
        return Ok(Source {
            reader: Box::new(io::stdin()),
            child: None,
        });
    };
    for decompressor in &DECOMPRESSORS {
        if !path.ends_with(decompressor.suffix) || !signed(path, decompressor.signature) {
            continue;
        }
        let spawned = Command::new(decompressor.program)
            .args(decompressor.args)
            .arg(path)
            .stdin(Stdio::null())
            .stdout(Stdio::piped())
            .stderr(Stdio::null())
            .spawn();
        if let Ok(mut child) = spawned {
            if let Some(stdout) = child.stdout.take() {
                return Ok(Source {
                    reader: Box::new(stdout),
                    child: Some(child),
                });
            }
        }
    }
    Ok(Source {
        reader: Box::new(File::open(path)?),
        child: None,
    })
}

fn signed(path: &str, signature: &[u8]) -> bool {
    let mut head = vec![0; signature.len()];
    File::open(path)
        .and_then(|mut file| file.read_exact(&mut head))
        .is_ok_and(|()| head == signature)
}

fn solve(run: &Run, out: &mut impl Write) -> Result<u8, Failure> {
    if let Some(opt) = unported(&run.options) {
        return Err(format!(
            "option '--{}={}' needs a part of Kissat not ported yet",
            opt.spec().name,
            run.options.get(opt)
        )
        .into());
    }
    let name = run.path.as_deref().unwrap_or(STDIN);
    let source =
        open(run.path.as_deref()).map_err(|_| format!("failed to open '{name}' for reading"))?;
    let quiet = run.options.get(Opt::Quiet) != OFF;
    let mut engine = engine(run)?;
    let mut originals = Vec::new();
    let mut invalid = None;
    let mut header_line = None;
    let mut dimacs = Dimacs::new(source.reader, run.strictness);
    let parsed = dimacs.header().and_then(|header| {
        if !quiet {
            header_line = Some(format!(
                "c parsed 'p cnf {} {}' header",
                header.variables, header.clauses
            ));
        }
        if let Err(error) = engine.reserve(header.variables.unsigned_abs()) {
            invalid.get_or_insert(error);
        }
        dimacs
            .clauses(header, |lit| {
                originals.push(lit);
                if let Err(error) = engine.add(lit) {
                    invalid.get_or_insert(error);
                }
            })
            .map(|()| header.variables)
    });
    if let Some(mut child) = source.child {
        let _ = child.wait();
    }
    if let Some(line) = header_line {
        writeln!(out, "{line}")?;
        out.flush()?;
    }
    let variables = parsed.map_err(|error| format!("{name}:{error}"))?;
    if let Some(error) = invalid {
        return Err(format!("{name}: {error}").into());
    }
    let outcome = engine.solve().map_err(|error| format!("{name}: {error}"))?;
    let mut counters = engine.solver().counters();
    if let Some(proof) = engine.take_proof() {
        counters.extend(proof.counters());
        proof.finish().map_err(Failure::Proof)?;
    }
    let code = match outcome {
        Outcome::Satisfiable => {
            check_model(engine.solver(), &originals)?;
            writeln!(out, "s SATISFIABLE")?;
            if run.witness {
                witness(engine.solver(), variables, out)?;
            }
            EXIT_SATISFIABLE
        }
        Outcome::Unsatisfiable => {
            writeln!(out, "s UNSATISFIABLE")?;
            EXIT_UNSATISFIABLE
        }
        Outcome::Unknown => {
            writeln!(out, "{UNKNOWN}")?;
            EXIT_UNKNOWN
        }
    };
    if !quiet {
        let verbosity = if run.options.get(Opt::Statistics) == OFF {
            Verbosity::Brief
        } else {
            Verbosity::Complete
        };
        for counter in counters {
            if counter.printed(verbosity) {
                let name = format!("{}:", counter.name);
                writeln!(out, "c {name:<NAME_WIDTH$} {:>VALUE_WIDTH$}", counter.value)?;
            }
        }
    }
    Ok(code)
}

fn open_proof(path: &str, format: Format) -> Result<Proof, String> {
    if path == STDOUT {
        return Ok(Proof::new(Box::new(io::stdout()), Format::Ascii));
    }
    let file =
        File::create(path).map_err(|_| format!("failed to open and write proof to '{path}'"))?;
    Ok(Proof::new(Box::new(BufWriter::new(file)), format))
}

fn most_likely_existing_cnf_file(path: &str) -> bool {
    File::open(path).is_ok()
        && CNF_SUFFIXES.iter().any(|cnf| {
            COMPRESSED_SUFFIXES
                .iter()
                .any(|compressed| path.ends_with(&format!("{cnf}{compressed}")))
        })
}

fn printed_value(solver: &Solver, eidx: i32) -> i32 {
    match solver.external_value(eidx) {
        0 => eidx,
        value => value,
    }
}

fn check_model(solver: &Solver, originals: &[i32]) -> Result<(), String> {
    let clauses = originals
        .split(|&lit| lit == 0)
        .filter(|clause| !clause.is_empty());
    for (number, clause) in clauses.enumerate() {
        if !clause
            .iter()
            .any(|&lit| printed_value(solver, lit.abs()) == lit)
        {
            return Err(format!(
                "satisfying assignment falsifies original clause {}",
                number + 1
            ));
        }
    }
    Ok(())
}

fn witness(solver: &Solver, variables: i32, out: &mut impl Write) -> io::Result<()> {
    let mut line = String::new();
    for value in (1..=variables)
        .map(|eidx| printed_value(solver, eidx))
        .chain([0])
    {
        let field = format!(" {value}");
        if line.len() + field.len() > WITNESS_WIDTH {
            writeln!(out, "v{line}")?;
            line.clear();
        }
        line.push_str(&field);
    }
    writeln!(out, "v{line}")
}

fn limit<'a>(
    arg: &'a str,
    value: &str,
    previous: &mut Option<&'a str>,
    least: u64,
) -> Result<u64, String> {
    let limit = parse_value(value)
        .and_then(|limit| u64::try_from(limit).ok())
        .filter(|&limit| limit >= least)
        .ok_or_else(|| format!("invalid argument in '{arg}' (try '-h')"))?;
    if let Some(previous) = previous.replace(arg) {
        return Err(format!("multiple '{previous}' and '{arg}'"));
    }
    Ok(limit)
}

fn help(out: &mut impl Write) -> io::Result<()> {
    writeln!(out, "{USAGE}\n")?;
    for limit in LIMITS {
        writeln!(out, "  {limit}")?;
    }
    writeln!(out)?;
    for configuration in Configuration::ALL {
        writeln!(
            out,
            "  --{:<8} {}",
            configuration.name(),
            configuration.help()
        )?;
    }
    writeln!(out)?;
    for spec in SPECS {
        writeln!(
            out,
            "  --{}=<{}..{}>  {} [{}]",
            spec.name, spec.low, spec.high, spec.help, spec.value
        )?;
    }
    Ok(())
}

#[derive(Debug, Error)]
enum Failure {
    #[error("{0}")]
    Message(String),
    #[error("writing the output failed: {0}")]
    Output(#[from] io::Error),
    #[error("writing the proof failed: {0}")]
    Proof(io::Error),
}

impl From<String> for Failure {
    fn from(message: String) -> Failure {
        Failure::Message(message)
    }
}

fn run(args: &[String], out: &mut impl Write) -> Result<u8, Failure> {
    match invocation(args)? {
        Action::Help => help(out)?,
        Action::Range => {
            for spec in SPECS.iter().filter(|spec| spec.opt.ranged()) {
                writeln!(
                    out,
                    "{} {} {} {}",
                    spec.name, spec.low, spec.value, spec.high
                )?;
            }
        }
        Action::Version => writeln!(
            out,
            "{} (port of Kissat {KISSAT_VERSION})",
            env!("CARGO_PKG_VERSION")
        )?,
        Action::Solve(run) => return solve(&run, out),
    }
    Ok(EXIT_UNKNOWN)
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mut out = BufWriter::new(io::stdout().lock());
    let ran = run(&args, &mut out);
    let flushed = out.flush().map_err(Failure::from);
    match ran.and_then(|code| flushed.map(|()| code)) {
        Ok(code) => ExitCode::from(code),
        Err(Failure::Output(error) | Failure::Proof(error))
            if error.kind() == ErrorKind::BrokenPipe =>
        {
            ExitCode::from(EXIT_BROKEN_PIPE)
        }
        Err(failure) => {
            eprintln!("xsat: error: {failure}");
            ExitCode::from(EXIT_ERROR)
        }
    }
}

enum Engine {
    One(Box<Solver>),
    Many(Portfolio),
}

fn engine(run: &Run) -> Result<Engine, String> {
    if run.workers > 1 {
        if run.proof.is_some()
            || run.conflicts.is_some()
            || run.decisions.is_some()
            || run.time.is_some()
        {
            return Err("proofs and limits need a single worker".to_owned());
        }
        return Ok(Engine::Many(Portfolio::new(&run.options, run.workers)));
    }
    let mut solver = Solver::new(run.options.clone());
    if let Some(limit) = run.conflicts {
        solver.limit_conflicts(limit);
    }
    if let Some(limit) = run.decisions {
        solver.limit_decisions(limit);
    }
    if let Some(seconds) = run.time {
        let terminator = solver.terminator();
        std::thread::spawn(move || {
            std::thread::sleep(Duration::from_secs(seconds));
            terminator.terminate();
        });
    }
    if let Some(path) = &run.proof {
        solver
            .trace_proof(open_proof(path, run.format)?)
            .map_err(|error| error.to_string())?;
    }
    Ok(Engine::One(Box::new(solver)))
}

impl Engine {
    fn reserve(&mut self, variables: u32) -> Result<(), SolverError> {
        match self {
            Engine::One(solver) => solver.reserve(variables),
            Engine::Many(portfolio) => portfolio.reserve(variables),
        }
    }

    fn add(&mut self, lit: i32) -> Result<(), SolverError> {
        match self {
            Engine::One(solver) => solver.add(lit),
            Engine::Many(portfolio) => portfolio.add(lit),
        }
    }

    fn solve(&mut self) -> Result<Outcome, SolverError> {
        match self {
            Engine::One(solver) => solver.solve(),
            Engine::Many(portfolio) => portfolio.solve(),
        }
    }

    fn solver(&self) -> &Solver {
        match self {
            Engine::One(solver) => solver,
            Engine::Many(portfolio) => portfolio.winner(),
        }
    }

    fn take_proof(&mut self) -> Option<Proof> {
        match self {
            Engine::One(solver) => solver.take_proof(),
            Engine::Many(_) => None,
        }
    }
}

fn workers(arg: &str, value: &str) -> Result<usize, String> {
    value
        .parse()
        .ok()
        .filter(|&workers| workers > 0)
        .ok_or_else(|| format!("invalid argument in '{arg}' (try '-h')"))
}
