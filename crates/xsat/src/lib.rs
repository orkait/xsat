mod cdcl;
pub mod dimacs;
pub mod error;
mod external;
mod incremental;
mod inprocess;
pub mod options;
pub mod parallel;
mod solver;
mod store;
mod trace;

pub use cdcl::{search::unported, terminate::Terminator};
pub use external::{
    propagator::{ExternalClause, Propagator},
    xor::{Gauss, Parity},
};
pub use solver::{Outcome, Solver, Statistics};
pub use trace::{proof, statistics};

pub const KISSAT_VERSION: &str = "4.0.4";
