# Porting map

xsat ports Kissat 4.0.4 (`/src` of the release tarball) function for function. A Rust item carries the Kissat name minus its `kissat_` or `kitten_` prefix, in the module named after the Kissat file. The directory says what the file is for: `store/` holds the data structures (arena, watches, assignment, clauses, flags, heap, queue), `solver.rs` the `Solver` itself with assignment and propagation, `cdcl/` the search loop and its heuristics (analysis, minimization, decisions, restarts, modes, phases, reduction, limits), `inprocess/` the simplification passes (probing, elimination, sweeping, congruence and the rest), `incremental/` assumptions and the reconstruction stack, `external/` the propagator interface and Gauss, `trace/` proofs and statistics. `analyze.c` is `cdcl/analyze.rs`, so `kissat_learn_clause` is `Solver::learn_clause` there. Code comments do not repeat these names; the items below are the ones the rule does not find.

| Kissat | xsat | Why it differs |
|---|---|---|
| `kissat_init_smooth` | `Smooth::new` | constructor |
| `kissat_update_smooth` | `Smooth::update` | method of its type |
| `kissat_init_averages` | `Averages::init` | method of its type |
| `kissat_update_queue` | `Queue::update` | method of its type |
| `kissat_reset_search_of_queue` | `Queue::reset_search` | method of its type |
| `kissat_reassign_queue_stamps` | `Queue::reassign_stamps` | method of its type |
| `kissat_reduce_delay`, `kissat_bump_delay` | `Delay::reduce`, `Delay::bump` | methods of their type |
| `resize_gate_hash_table` | `Closure::resize` | method of its type |
| `kissat_probing` | `Solver::probing_due` | the name alone reads as the pass |
| `non_watching_propagate_literal` | `Solver::dense_propagate_literal` | named after the dense mode it runs in |
| `rephase_schedule` | `rephase::SCHEDULE` | a constant table |
| `kissat_print_proof_statistics` | `Proof::counters` | returns the counters instead of printing |
| `--incremental` | accepted, no effect | xsat always keeps the extension stack as Kissat does with `--incremental=1`: weakened clauses only, no unit witnesses, so clauses added after a solve can restore eliminated variables soundly |
| `kissat_set_terminate` | not ported | Kissat 4.0.4 stores the callback but never calls it; `Solver::terminator` returns a `Terminator` whose `terminate` sets the flag every `TERMINATED` site reads |
| `--time=` given twice | rejected as `multiple` | `application.c` checks `time_option` but never sets it, so Kissat keeps the last value; xsat treats it like `--conflicts=` and `--decisions=` |
| parse errors in the clause section | report the line of the error; `xsat-dev parse` and `mutate` compare the fault text, not the line | Kissat 4.0.4 reports line 1 for most of them (arminbiere/kissat#83: plain `return`s in `parse_dimacs` skip copying the line counter) |
| `Solver::add`, `freeze`, `solve_assuming`, `connect` | return `LiteralError` for 0 (where a literal is required), `i32::MIN` or a variable above 2^30 - 1 | `kissat_add` aborts the process through `kissat_require`; a library returns the error |
