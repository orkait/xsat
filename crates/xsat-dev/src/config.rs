use std::path::PathBuf;

const JOBS_VAR: &str = "XSAT_JOBS";
const JOBS: usize = 4;
const KISSAT_VAR: &str = "XSAT_KISSAT";
const KISSAT: &str = "kissat";
const IDRUP_CHECK_VAR: &str = "XSAT_IDRUP_CHECK";
const IDRUP_CHECK: &str = "idrup-check";
const DRAT_TRIM_VAR: &str = "XSAT_DRAT_TRIM";
const DRAT_TRIM: &str = "drat-trim";
const LRAT_CHECK_VAR: &str = "XSAT_LRAT_CHECK";
const LRAT_CHECK: &str = "lrat-check";

fn tool(var: &str, default: &str) -> PathBuf {
    std::env::var_os(var).map_or_else(|| PathBuf::from(default), PathBuf::from)
}

pub(crate) fn kissat() -> PathBuf {
    tool(KISSAT_VAR, KISSAT)
}

pub(crate) fn idrup_check() -> PathBuf {
    tool(IDRUP_CHECK_VAR, IDRUP_CHECK)
}

pub(crate) fn drat_trim() -> PathBuf {
    tool(DRAT_TRIM_VAR, DRAT_TRIM)
}

pub(crate) fn lrat_check() -> PathBuf {
    tool(LRAT_CHECK_VAR, LRAT_CHECK)
}

pub(crate) fn jobs() -> usize {
    std::env::var(JOBS_VAR)
        .ok()
        .and_then(|jobs| jobs.parse().ok())
        .unwrap_or(JOBS)
}
