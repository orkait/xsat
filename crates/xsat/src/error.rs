use std::io;

use thiserror::Error;

const RELAXED_HINT: &str = "(try '--relaxed' parsing)";

#[derive(Debug, Error)]
pub enum OptionError {
    #[error("value {value} of option '{name}' out of range")]
    Range { name: &'static str, value: i32 },
}

#[derive(Debug, Error)]
pub enum SolverError {
    #[error("invalid literal {0}")]
    InvalidLiteral(i32),
    #[error("incomplete clause (terminating zero not added)")]
    IncompleteClause,
    #[error("invalid maximum variable argument '{0}'")]
    InvalidMaximumVariable(u32),
    #[error("a proof must be attached before any input, solve or propagator")]
    ProofAfterInput,
    #[error("assumptions need an IDRUP proof, not DRAT")]
    AssumptionsNeedIdrup,
    #[error("adding clauses after a solve needs an IDRUP proof, not DRAT")]
    InputAfterSolveNeedsIdrup,
    #[error("an external propagator cannot be combined with a proof")]
    PropagatorWithProof,
}

#[derive(Debug, Error)]
#[error("{line}: parse error: {fault}")]
pub struct ParseError {
    pub line: u64,
    pub fault: Fault,
}

#[derive(Debug, Error)]
pub enum Fault {
    #[error("empty file")]
    Empty,
    #[error("end-of-file before header")]
    EofBeforeHeader,
    #[error("expected new-line after carriage-return")]
    CarriageReturn,
    #[error("unexpected empty line")]
    EmptyLine,
    #[error("end-of-file in header comment")]
    EofInHeaderComment,
    #[error("expected 'c' or 'p' at start of line")]
    LineStart,
    #[error("expected space after 'p'")]
    SpaceAfterP,
    #[error("expected 'c' after 'p '")]
    CAfterP,
    #[error("expected 'n' after 'p c'")]
    NAfterPC,
    #[error("expected 'n' after 'p cn'")]
    FAfterPCn,
    #[error("expected space after 'p cnf'")]
    SpaceAfterCnf,
    #[error("expected digit after 'p cnf '")]
    DigitAfterCnf,
    #[error("maximum variable too large")]
    MaxVariableTooLarge,
    #[error("unexpected end-of-file while parsing maximum variable")]
    EofInMaxVariable,
    #[error("unexpected new-line after maximum variable")]
    NewLineAfterMaxVariable,
    #[error("expected space after maximum variable")]
    SpaceAfterMaxVariable,
    #[error("expected number of clauses after maximum variable")]
    ClausesAfterMaxVariable,
    #[error("number of clauses too large")]
    ClausesTooLarge,
    #[error("unexpected end-of-file while parsing number of clauses")]
    EofInClauses,
    #[error("unexpected end-of-file after parsing number of clauses")]
    EofAfterClauses,
    #[error("expected new-line after parsing number of clauses")]
    NewLineAfterClauses,
    #[error("unexpected end-of-file in comment after header")]
    EofInCommentAfterHeader,
    #[error("unexpected end-of-file after '-'")]
    EofAfterMinus,
    #[error("unexpected new-line after '-'")]
    NewLineAfterMinus,
    #[error("expected digit after '-'")]
    DigitAfterMinus,
    #[error("expected non-zero digit after '-'")]
    NonZeroAfterMinus,
    #[error("expected digit or '-'")]
    DigitOrMinus,
    #[error("variable index too large")]
    IndexTooLarge,
    #[error("unexpected end-of-file after literal")]
    EofAfterLiteral,
    #[error("unexpected end-of-file after trailing zero")]
    EofAfterZero,
    #[error("unexpected end-of-file in comment after literal")]
    EofInCommentAfterLiteral,
    #[error("expected white space after literal")]
    SpaceAfterLiteral,
    #[error("maximum variable index exceeded {RELAXED_HINT}")]
    IndexExceeded,
    #[error("too many clauses {RELAXED_HINT}")]
    TooManyClauses,
    #[error("trailing zero missing")]
    TrailingZero,
    #[error("one clause missing {RELAXED_HINT}")]
    OneClauseMissing,
    #[error("more than one clause missing {RELAXED_HINT}")]
    ClausesMissing,
    #[error("read failed: {0}")]
    Read(#[from] io::Error),
}
