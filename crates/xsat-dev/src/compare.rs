use std::{
    path::{Path, PathBuf},
    process::Command,
    time::Duration,
};

use crate::{
    config,
    error::DevError,
    process::{self, Ran, TempDir},
    random::Random,
};

const USAGE: &str =
    "xsat-dev range | parse <dimacs>... | solve <--option>... <dimacs>... | mutate [--cases N] [--seed N] <dimacs>... | assume [--cases N] [--seed N] | prove <dimacs>...";
const XSAT_PACKAGE: &str = "xsat-cli";
const XSAT_BINARY: &str = "xsat";
const RELEASE: &str = "target/release";
const CRATE_DEPTH: usize = 2;
const DEADLINE: Duration = Duration::from_secs(60);
const KISSAT_PREFIX: &str = "kissat:";
const XSAT_PREFIX: &str = "xsat:";
const HEADER: &str = "c parsed 'p cnf";
const PARSE_ERROR: &str = "parse error: ";
const RANGE: &str = "--range";
const EXIT_ERROR: i32 = 1;
const SOLVE_DEADLINE: Duration = Duration::from_secs(600);
const BASIC: &str = "--basic";
const OPTION_PREFIX: &str = "--";
const STATISTICS: &str = "-s";
const STATUS: &str = "s ";
const COMMENT: &str = "c ";
const COUNTERS: [&str; 4] = ["conflicts", "decisions", "propagations", "search_ticks"];
const NO_SEARCH: [&str; 5] = [
    BASIC,
    "--conflicts=0",
    "--preprocess=false",
    "--lucky=false",
    "--warmup=false",
];
const STRICTNESS: [Option<&str>; 3] = [None, Some("--relaxed"), Some("--strict")];
const ALPHABET: &[u8] = b" \t\n\r-0123456789cpnfx";
const EDITS: (i64, i64) = (1, 5);
const DEFAULT_CASES: usize = 1000;
const SHOWN: usize = 5;
const SHOWN_BYTES: usize = 240;

#[derive(Clone, Copy)]
enum Edit {
    Replace,
    Insert,
    Delete,
    Truncate,
}

#[derive(Debug, PartialEq, Eq)]
struct Parsed {
    failed: bool,
    header: Option<String>,
    error: Option<String>,
}

struct Case {
    path: PathBuf,
    strictness: Option<&'static str>,
}

fn workspace() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .ancestors()
        .nth(CRATE_DEPTH)
        .map_or_else(|| PathBuf::from("."), Path::to_path_buf)
}

fn xsat() -> Result<PathBuf, DevError> {
    let binary = workspace().join(RELEASE).join(XSAT_BINARY);
    if binary.exists() {
        Ok(binary)
    } else {
        Err(DevError::Binary(binary, XSAT_PACKAGE))
    }
}

fn parsed(ran: &Ran, prefix: &str) -> Parsed {
    let stdout = String::from_utf8_lossy(&ran.stdout);
    let stderr = String::from_utf8_lossy(&ran.stderr);
    Parsed {
        failed: ran.code == EXIT_ERROR,
        header: stdout
            .lines()
            .find(|line| line.starts_with(HEADER))
            .map(str::to_owned),
        error: stderr
            .lines()
            .find_map(|line| line.strip_prefix(prefix))
            .map(|error| {
                error
                    .split_once(PARSE_ERROR)
                    .map_or(error, |(_, fault)| fault)
            })
            .map(str::to_owned),
    }
}

fn observe(
    binary: &Path,
    extra: &[&str],
    prefix: &str,
    case: &Case,
) -> Result<Option<Parsed>, DevError> {
    let mut command = Command::new(binary);
    command.args(extra).args(case.strictness).arg(&case.path);
    Ok(process::run(&mut command, DEADLINE)?.map(|ran| parsed(&ran, prefix)))
}

fn compare(kissat: &Path, xsat: &Path, case: &Case) -> Result<Option<String>, DevError> {
    let reference = observe(kissat, &NO_SEARCH, KISSAT_PREFIX, case)?;
    let ported = observe(xsat, &NO_SEARCH, XSAT_PREFIX, case)?;
    if reference.is_some() && reference == ported {
        return Ok(None);
    }
    Ok(Some(format!(
        "{} {}: kissat {reference:?}, xsat {ported:?}",
        case.path.display(),
        case.strictness.unwrap_or_default()
    )))
}

pub(crate) fn report(differences: &[String], total: usize, what: &str) -> bool {
    for difference in differences.iter().take(SHOWN) {
        println!("DIFFER {difference}");
    }
    println!(
        "{}/{total} {what} in kissat and xsat",
        total - differences.len()
    );
    differences.is_empty()
}

fn compared(kissat: &Path, xsat: &Path, cases: &[Case]) -> Result<Vec<String>, DevError> {
    process::parallel(cases, config::jobs(), |case| compare(kissat, xsat, case))?
        .into_iter()
        .filter_map(Result::transpose)
        .collect()
}

fn range(kissat: &Path, xsat: &Path) -> Result<bool, DevError> {
    let listed = |binary: &Path| -> Result<Vec<u8>, DevError> {
        let ran = process::run(Command::new(binary).arg(RANGE), DEADLINE)?
            .ok_or(DevError::Failed(RANGE))?;
        Ok(ran.stdout)
    };
    let same = listed(kissat)? == listed(xsat)?;
    println!(
        "option range lists {}",
        if same { "identical" } else { "DIFFER" }
    );
    Ok(same)
}

fn mutated(rng: &mut Random, seed: &[u8]) -> Vec<u8> {
    let mut bytes = seed.to_vec();
    for _ in 0..rng.randrange(EDITS.0, EDITS.1) {
        let at = usize::try_from(rng.randrange(0, i64::try_from(bytes.len()).unwrap_or_default()))
            .unwrap_or_default();
        let byte = rng.pick_from(ALPHABET).unwrap_or_default();
        match rng.pick([Edit::Replace, Edit::Insert, Edit::Delete, Edit::Truncate]) {
            Edit::Replace if at < bytes.len() => bytes[at] = byte,
            Edit::Insert | Edit::Replace => bytes.insert(at, byte),
            Edit::Delete if at < bytes.len() => {
                bytes.remove(at);
            }
            Edit::Delete => {}
            Edit::Truncate => bytes.truncate(at),
        }
    }
    bytes
}

fn mutate(kissat: &Path, xsat: &Path, args: &[String]) -> Result<bool, DevError> {
    let (mut count, mut seed, mut sources) = (DEFAULT_CASES, 0_u64, Vec::new());
    let mut args = args.iter();
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--cases" => count = number(args.next())?,
            "--seed" => seed = number(args.next())?,
            _ => sources.push(std::fs::read(arg)?),
        }
    }
    if sources.is_empty() {
        return Err(DevError::Usage(USAGE));
    }
    let dir = TempDir::new("xsat-mutate")?;
    let numbers: Vec<u64> = (0..count).filter_map(|at| u64::try_from(at).ok()).collect();
    let outcomes = process::parallel(&numbers, config::jobs(), |&number| {
        let mut rng = Random::new(seed.wrapping_add(number));
        let source = rng.pick_from(&sources).unwrap_or_default();
        let bytes = mutated(&mut rng, &source);
        let case = Case {
            path: dir.path().join(format!("case{number}.cnf")),
            strictness: rng.pick(STRICTNESS),
        };
        std::fs::write(&case.path, &bytes)?;
        let compared = compare(kissat, xsat, &case);
        std::fs::remove_file(&case.path)?;
        Ok::<_, DevError>(compared?.map(|difference| {
            let head = bytes.get(..SHOWN_BYTES).unwrap_or(&bytes);
            format!(
                "{difference}\n  case {number}: {:?}",
                String::from_utf8_lossy(head)
            )
        }))
    })?;
    let differences: Vec<String> = outcomes
        .into_iter()
        .filter_map(Result::transpose)
        .collect::<Result<_, _>>()?;
    Ok(report(&differences, count, "mutated files parse alike"))
}

fn trace(ran: &Ran) -> Vec<String> {
    String::from_utf8_lossy(&ran.stdout)
        .lines()
        .filter_map(|line| {
            if line.starts_with(STATUS) {
                return Some(line.trim_end().to_owned());
            }
            let (name, value) = line.strip_prefix(COMMENT)?.split_once(':')?;
            let value = value.split_whitespace().next()?;
            COUNTERS.contains(&name).then(|| format!("{name} {value}"))
        })
        .collect()
}

fn solved(
    kissat: &Path,
    xsat: &Path,
    options: &[String],
    path: &Path,
) -> Result<Option<String>, DevError> {
    let run = |binary: &Path| -> Result<Option<Vec<String>>, DevError> {
        let mut command = Command::new(binary);
        command.args(options).arg(STATISTICS).arg(path);
        Ok(process::run(&mut command, SOLVE_DEADLINE)?.map(|ran| trace(&ran)))
    };
    let reference = run(kissat)?;
    let ported = run(xsat)?;
    if reference.is_some() && reference == ported {
        return Ok(None);
    }
    Ok(Some(format!(
        "{}: kissat {reference:?}, xsat {ported:?}",
        path.display()
    )))
}

fn number<T: std::str::FromStr>(value: Option<&String>) -> Result<T, DevError> {
    value
        .and_then(|value| value.parse().ok())
        .ok_or(DevError::Usage(USAGE))
}

pub(crate) fn main(args: &[String]) -> Result<bool, DevError> {
    let kissat = config::kissat();
    let xsat = xsat()?;
    match args.split_first() {
        Some((mode, [])) if mode == "range" => range(&kissat, &xsat),
        Some((mode, files)) if mode == "parse" && !files.is_empty() => {
            let cases: Vec<Case> = files
                .iter()
                .map(|file| Case {
                    path: PathBuf::from(file),
                    strictness: None,
                })
                .collect();
            let differences = compared(&kissat, &xsat, &cases)?;
            Ok(report(&differences, cases.len(), "files parse alike"))
        }
        Some((mode, rest)) if mode == "solve" => {
            let (options, files) = rest.split_at(
                rest.iter()
                    .position(|arg| !arg.starts_with(OPTION_PREFIX))
                    .unwrap_or(rest.len()),
            );
            if options.is_empty() || files.is_empty() {
                return Err(DevError::Usage(USAGE));
            }
            let differences: Vec<String> = process::parallel(files, config::jobs(), |file| {
                solved(&kissat, &xsat, options, Path::new(file))
            })?
            .into_iter()
            .filter_map(Result::transpose)
            .collect::<Result<_, _>>()?;
            Ok(report(
                &differences,
                files.len(),
                "files solve with identical counters",
            ))
        }
        Some((mode, rest)) if mode == "mutate" => mutate(&kissat, &xsat, rest),
        Some((mode, rest)) if mode == "assume" => crate::sessions::assume(&kissat, rest),
        Some((mode, files)) if mode == "prove" && !files.is_empty() => {
            crate::lrat::prove(&xsat, files)
        }
        _ => Err(DevError::Usage(USAGE)),
    }
}
