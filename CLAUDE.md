# zsat — PROJECT MEMORY & CORE RULES

Zero-allocation hardened SAT solver in Rust (bounded CDCL + SLS + probing + FSM/Q-table
controller). Overview and measured results: `README.md`. Deadline design:
`docs/references/deadline-contract.md`.

## Commands
- Build: `cargo build --release` (must stay warning-free); audit build: `--features checked`
- Tests: `cargo test` (debug), `cargo test --release`, `cargo test --release --features checked`
  (`deadline_respected_on_mid_instance` is release-only)
- Self-test: `./target/release/zsat --selftest 3000` (also `1500` with `--no-relax`,
  `--steepest`, `--no-learning`; all must print `failures=0`)
- Bench: `./target/release/zsat --bench --timeout 10000` (verdicts, `allocs-in-solve=0`)
- Deadline: `./target/release/zsat --deadline-check` (exit 1 on overshoot)
- Solve a file: `zsat file.cnf --timeout MS --mem MiB [--model] [--log]`; exit 10/20/0 = SAT/UNSAT/UNKNOWN

## Hard rules
- `solve()` must never allocate. No `Vec`/`Box`/`String`/`format!`/`eprintln!` on its path
  (harness and tests arm a counting allocator).
- No clock reads in `propagate()` (hot loop). Account work via `stats.propagations` around it.
- Unchecked indexing (`at`/`at_mut`) relies on load-time validation; keep the invariant.
- Out of scope unless asked: SLS/CDCL/Q-table tuning, DRAT, portfolio overhead.

## Soundness invariants
1. `Sat` only after `verify_model_strict()` gives u == 0 on the pristine copy; that eval never stops early.
2. `Unsat` only via `on_root_conflict()`.
3. `best_unsat` == violated count of `best`; an aborted eval must not touch either.
4. `root_simplify_and_rebuild()` and `reduce_db()` are atomic; optional callers may only decline to start.
5. No clock in `propagate()`.
6. `solve()` allocates nothing; no debug formatting left in its path.
7. `pure_literal_pass`: once enqueueing starts it finishes and a rebuild follows; it may stop only while counting.
8. A stopped `subsumption_pass` only ever deleted clauses proven subsumed.

## Deadline model (details in docs/references/deadline-contract.md)
`Config::timeout_ms` -> `deadline`; `preprocess_budget_ppm` (15 %) caps optional pre/in-processing;
final eval gets `grace = clamp(timeout/20, 5, 50)` ms; past the deadline the loop skips tighten/FSM/inprocess.
UNKNOWN without an evaluated assignment: `has_best() == false`, `best_unsat == u32::MAX`.

## Module map (see README.md "Layout")
`types` (Lit, Config, EventKind) · `arena` (Formula, Layout, SolverWorkspace) · `util` (BitSet, Rng, Ticker, EventLog)
· `propagate` (2WL, root rebuild) · `order` (decision tree) · `cdcl` · `sls` · `lookahead` (probing)
· `preprocess` (UP, pure, subsumption) · `controller` (FSM + Q-table) · `solver` (relaxation, anytime best, main loop)
· `main.rs` (harness, generators, selftest, bench, deadline-check).
