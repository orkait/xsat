use std::{path::Path, process::Command, time::Duration};

use crate::{
    compare::report,
    config,
    error::DevError,
    process::{self, TempDir},
};

const DEADLINE: Duration = Duration::from_secs(600);
const SATISFIABLE: i32 = 10;
const UNSATISFIABLE: i32 = 20;
const DRAT_VERIFIED: &str = "s VERIFIED";
const LRAT_VERIFIED: &str = "c VERIFIED";

fn verified(command: &mut Command, verdict: &str) -> Result<bool, DevError> {
    Ok(process::run(command, DEADLINE)?
        .is_some_and(|ran| ran.code == 0 && String::from_utf8_lossy(&ran.stdout).contains(verdict)))
}

fn proved(xsat: &Path, dir: &Path, cnf: &Path) -> Result<Option<String>, DevError> {
    let name = cnf
        .file_name()
        .map(|name| name.to_string_lossy().into_owned())
        .unwrap_or_default();
    let drat = dir.join(format!("{name}.drat"));
    let lrat = dir.join(format!("{name}.lrat"));
    let solved = process::run(
        Command::new(xsat).arg("-q").arg("-n").arg(cnf).arg(&drat),
        DEADLINE,
    )?;
    let fault = match solved.map(|ran| ran.code) {
        Some(SATISFIABLE) => None,
        Some(UNSATISFIABLE) => {
            if !verified(
                Command::new(config::drat_trim())
                    .arg(cnf)
                    .arg(&drat)
                    .arg("-L")
                    .arg(&lrat),
                DRAT_VERIFIED,
            )? {
                Some(format!("{name}: drat-trim did not verify the DRAT proof"))
            } else if !verified(
                Command::new(config::lrat_check()).arg(cnf).arg(&lrat),
                LRAT_VERIFIED,
            )? {
                Some(format!("{name}: lrat-check did not verify the LRAT proof"))
            } else {
                None
            }
        }
        code => Some(format!("{name}: xsat ended with {code:?}")),
    };
    for path in [&drat, &lrat] {
        if path.exists() {
            std::fs::remove_file(path)?;
        }
    }
    Ok(fault)
}

pub(crate) fn prove(xsat: &Path, files: &[String]) -> Result<bool, DevError> {
    let dir = TempDir::new("xsat-lrat")?;
    let faults: Vec<String> = process::parallel(files, config::jobs(), |file| {
        proved(xsat, dir.path(), Path::new(file))
    })?
    .into_iter()
    .filter_map(Result::transpose)
    .collect::<Result<_, _>>()?;
    Ok(report(
        &faults,
        files.len(),
        "files have xsat proofs that lrat-check accepts",
    ))
}
