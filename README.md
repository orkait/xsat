<div align="center">

# xsat

**Kissat's CDCL search in safe Rust, with incremental solving, checked proofs and pluggable theories.**

[![Rust 1.85+](https://img.shields.io/badge/Rust-1.85%2B-000000?style=for-the-badge&logo=rust&logoColor=white)](Cargo.toml)
[![Safe Rust](https://img.shields.io/badge/unsafe-forbidden-1f883d?style=for-the-badge&logo=rust&logoColor=white)](Cargo.toml)
[![Kissat 4.0.4](https://img.shields.io/badge/Kissat_4.0.4-identical_search-0969da?style=for-the-badge)](docs/verification.svg)
[![License](https://img.shields.io/badge/license-Apache--2.0_%2B_MIT-6e7781?style=for-the-badge)](#-license)

[Quickstart](#-quickstart) · [Features](#-features) · [Library](#-library) · [Architecture](#-architecture) · [Correctness](#-correctness)

</div>

xsat is a SAT solver for DIMACS CNF, usable as a command line tool and as a Rust library. Its search is a function-for-function port of [Kissat 4.0.4](https://github.com/arminbiere/kissat): on the default configuration it reaches the same answers through the same conflicts, decisions and propagations, and writes byte-identical DRAT proofs. Around that core it adds what Kissat does not offer: assumptions with failed-literal cores, clauses added between solves, IDRUP proofs for incremental sessions, an external propagator interface, Gaussian elimination over XOR constraints, and a deterministic parallel portfolio.

## 🚀 Quickstart

```sh
git clone https://github.com/orkait/xsat.git && cd xsat
cargo build --release
./target/release/xsat tests/corpus/r3_n50_s1.cnf
```

xsat prints `s SATISFIABLE` with the model in `v` lines, or `s UNSATISFIABLE`, and exits with 10 or 20 like Kissat. A second file name writes a DRAT proof:

```sh
./target/release/xsat -q tests/corpus/r3_n50_s1.cnf proof.drat
```

## ✨ Features

| | |
|---|---|
| 🔁 **Kissat's search** | focused and stable modes, VMTF and score heap, restarts, clause reduction, rephasing, chronological backtracking, warmup, local search |
| 🧹 **Inprocessing** | probing, backbones, transitive reduction, equivalence substitution, vivification, sweeping, congruence closure, bounded variable addition, bounded variable elimination |
| 🧾 **Proofs** | DRAT in binary and ASCII, IDRUP for incremental sessions, LRAT through `drat-trim` |
| ➕ **Incremental** | `solve_assuming` with failed-literal cores, `freeze` and `melt`, new clauses between solves |
| 🧩 **Extensible** | `Propagator` trait for external theories, built-in Gauss-Jordan for XOR constraints |
| ⚡ **Parallel** | `--workers=N` runs a diversified portfolio with the same answer and model on every run |
| 🛡️ **Safe** | `unsafe` is forbidden; clippy's `pedantic` group is denied |

## 📚 Library

```toml
[dependencies]
xsat = { git = "https://github.com/orkait/xsat.git" }
```

```rust
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
```

Run it with `cargo run --example quickstart`. Literals are non-zero `i32` values as in DIMACS and `0` ends a clause; invalid input comes back as a `SolverError`.

<details>
<summary><b>Proofs, propagators, limits and parallel solving</b></summary>

| Need | API |
|---|---|
| DRAT or IDRUP proof | `trace_proof(Proof::new(writer, Format::Idrup))` before adding clauses, then `take_proof()` and `finish()` |
| external theory | implement `Propagator` and pass it to `connect` |
| XOR constraints | `connect(Box::new(Gauss::new(&[(vec![1, 2, 3], Parity::Odd)])?))` |
| stop from another thread | `solver.terminator().terminate()` |
| budgets | `limit_conflicts(n)`, `limit_decisions(n)` |
| parallel | `parallel::Portfolio::new(&options, workers)`, then `add`, `solve`, `winner()` |

</details>

<details>
<summary><b>Command line options</b></summary>

```sh
xsat [ <option> ... ] [ <dimacs> [ <proof> ] ]
```

| Option | Effect |
|---|---|
| `-q`, `-n`, `-s` | quiet, no model, full statistics |
| `--sat`, `--unsat`, `--plain`, `--basic` | Kissat's configurations |
| `--<option>=<value>` | any of Kissat's options; `xsat --help` lists them with ranges |
| `--conflicts=`, `--decisions=`, `--time=` | stop with `s UNKNOWN` at a limit |
| `--workers=<n>` | parallel portfolio |
| `--no-binary` | ASCII DRAT |
| `--relaxed`, `--strict` | DIMACS parsing mode |

Compressed input is read through `gzip`, `bzip2`, `xz`, `lzma` and `7z`.

</details>

## 🏗️ Architecture

![xsat architecture](docs/architecture.svg)

Each source file is named after the Kissat file it ports: `cdcl/analyze.rs` is `analyze.c`, and `kissat_learn_clause` is `Solver::learn_clause`. [`PORTING.md`](PORTING.md) records the few deliberate differences.

<details>
<summary><b>One conflict, step by step</b></summary>

![conflict pipeline](docs/conflict.svg)

</details>

## ✅ Correctness

![verification](docs/verification.svg)

`xsat-dev` holds xsat to Kissat and to independent proof checkers:

| Command | Holds |
|---|---|
| `xsat-dev solve --preprocess=1 <cnf>...` | same answer and the same conflict, decision, propagation and tick counts as Kissat |
| `xsat-dev parse`, `mutate`, `range` | same parse results and option ranges as Kissat, also on corrupted input |
| `xsat-dev assume` | random incremental sessions agree with Kissat step by step; `idrup-check` accepts the proofs |
| `xsat-dev prove <cnf>...` | `lrat-check` accepts the LRAT that `drat-trim` derives from xsat's DRAT |

Point `XSAT_KISSAT`, `XSAT_IDRUP_CHECK`, `XSAT_DRAT_TRIM` and `XSAT_LRAT_CHECK` at the tools, or put them on `PATH`.

On SAT Competition 2025 instances xsat runs within a few percent of Kissat; see [`docs/benchmarks.md`](docs/benchmarks.md).

## 🗺️ Roadmap

| Next | |
|---|---|
| C ABI and IPASIR | use xsat from C, C++ and other languages |
| `fastel`, `factorstructural`, `sweeprand` | the last three Kissat options, all off by default |
| `-v` progress lines and `--partial` | the remaining Kissat CLI output |

## 🤝 Contributing

```sh
cargo +nightly fmt --all --check
cargo clippy --workspace --all-targets --all-features -- -D warnings
cargo build --release
XSAT_KISSAT=/path/to/kissat ./target/release/xsat-dev solve --preprocess=1 tests/corpus/*.cnf
```

A change to the search keeps the counters identical to Kissat; an intended difference goes into `PORTING.md`.

## 📄 License

Apache-2.0, see [LICENSE](LICENSE). xsat is a port of [Kissat](https://github.com/arminbiere/kissat) by Armin Biere and contributors, whose MIT license is in [LICENSE-KISSAT](LICENSE-KISSAT).
