use xsat::{error::SolverError, options::Options, Solver};

fn main() -> Result<(), SolverError> {
    let mut solver = Solver::new(Options::default());
    for clause in [[1, 2], [-1, 2], [-2, 3]] {
        for lit in clause {
            solver.add(lit)?;
        }
        solver.add(0)?;
    }
    let outcome = solver.solve()?;
    println!("{outcome:?}: x3 = {}", solver.external_value(3));

    let outcome = solver.solve_assuming(&[-3])?;
    println!("assuming -3: {outcome:?}, core {:?}", solver.core());
    Ok(())
}
