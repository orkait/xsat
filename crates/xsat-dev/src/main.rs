use std::process::ExitCode;

mod compare;
mod config;
mod error;
mod lrat;
mod process;
mod random;
mod serve;
mod sessions;

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match compare::main(&args) {
        Ok(true) => ExitCode::SUCCESS,
        Ok(false) => ExitCode::FAILURE,
        Err(error) => {
            eprintln!("{error}");
            ExitCode::FAILURE
        }
    }
}
