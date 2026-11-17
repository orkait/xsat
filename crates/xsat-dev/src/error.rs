use std::{io, path::PathBuf};

use thiserror::Error;

#[derive(Debug, Error)]
pub(crate) enum DevError {
    #[error("usage: {0}")]
    Usage(&'static str),
    #[error("missing {path}, run: cargo build --release -p {package}", path = .0.display(), package = .1)]
    Binary(PathBuf, &'static str),
    #[error("{0} failed")]
    Failed(&'static str),
    #[error(transparent)]
    Io(#[from] io::Error),
    #[error(transparent)]
    Solver(#[from] xsat::error::SolverError),
    #[error(transparent)]
    Option(#[from] xsat::error::OptionError),
}
