# zsat — zero-allocation hardened SAT solver (Rust)

Bounded CDCL + probSAT-style local search + failed-literal probing + in-processing,
orchestrated by a 3-mode FSM with hysteresis and a Q-table bandit. Every byte is
planned and budget-checked at load time; `solve()` performs **zero heap
allocations** (enforced by a counting global allocator in the harness and tests).

```
cargo build --release
./target/release/zsat --selftest 3000            # brute force + DPLL cross-check
./target/release/zsat --bench --timeout 10000     # built-in suite
./target/release/zsat --deadline-check            # solve() overshoot past --timeout (mid + 2M-var instances)
./target/release/zsat file.cnf --timeout 5000 --mem 256 --log --model
cargo test --release                              # integration tests
cargo build --release --features checked          # bounds-checked hot loops (audit mode)
```

Exit codes follow SAT-competition convention: 10 = SAT, 20 = UNSAT, 0 = UNKNOWN, 1 = harness failure.

## Layout

| File | Contents |
|---|---|
| `types.rs` | `Lit` (`var<<1 \| sign`), 16-byte `ClauseHeader`, 8-byte `WatchNode`, `Mode`/`Action`/`Event` (all `Copy`, heap-free), `Config` |
| `arena.rs` | `Formula` (load-time CSR), `Layout::bytes()` — exact byte plan checked against the budget **before** allocating (learnt arena shrinks to fit, else `LoadError::OverBudget`), `SolverWorkspace` owning every array; `Hot`/`Stats` are `#[repr(C, align(64))]` |
| `util.rs` | `at`/`at_mut` unchecked indexing (debug-asserted, `checked` feature restores bounds checks), `BitSet` over `#[repr(C, align(64))]` 512-bit lines with popcount, XorShift64\*, clock-amortised work-weighted `Ticker` (`tick_n`), fixed ring-buffer `EventLog` |
| `propagate.rs` | 2WL propagation over **intrusive fixed watch lists** (node `2c+w`, O(1) relink, blockers, lazy unlink of dead clauses); level-0 simplify + full watch rebuild |
| `order.rs` | Module 4: flat `u32` scores + segment-tree decision queue (early-exit path updates, no heap), bitwise decay via increment doubling + periodic `>>=` rescale |
| `cdcl.rs` | 1-UIP analysis, local minimisation, LBD; fixed learnt arena reduced **in place** (LBD histogram threshold, `copy_within` compaction); Luby restarts |
| `sls.rs` | Module 2: packed 16-byte per-clause record {true_count, true_xor, weight, pos}; XOR trick gives the critical variable for O(1) break updates; lazy best snapshot via flip trail; resumable across epochs |
| `lookahead.rs` | Module 3: top-K probing (fixed insertion buffer), failed literals, both-polarity implied literals, dead-end penalties |
| `preprocess.rs` | Module 6: UP, pure literals, 64-bit-signature subsumption; re-run on tier changes |
| `controller.rs` | Module 7: FSM (min dwell + asymmetric 2-up / 3-down streaks), `[f32; 6×6]` Q-table with ERWA update, bounded reward |
| `solver.rs` | Modules 1 & 5: masking, k-relaxation, iterative strengthening (halve k, unmask top-weight 15% via log2 histogram), anytime best, strict verification, main loop |
| `main.rs` | Harness: counting allocator, generators, DIMACS, independent model check, brute-force + DPLL self-test, benchmarks, deadline check, Q-table/transition printout |

## Soundness contract

- **SAT** only after forcing Conservative mode, unmasking 100% of clauses, `k = 0`, and evaluating the model against the *pristine* clause copy (never simplified) with popcount = 0. The harness re-checks every model against the raw input independently.
- **UNSAT** only from a level-0 conflict, after escalation to Conservative / 100% / `k = 0`. Root facts and learnt clauses are implications of a *subset* of the original clauses (or satisfiability-preserving pure-literal steps), so a conflict found while relaxed is already a refutation; escalation re-checks it strictly.
- Otherwise **UNKNOWN**. If any assignment was evaluated (`has_best()`), the best-so-far assignment and its exact violated-clause count are reported; an evaluation cut off by the deadline never updates them. If the deadline hit before the first evaluation (huge instance, tiny timeout), `has_best()` is false: `best_unsat == u32::MAX` is a sentinel, the harness prints `no assignment evaluated within budget`, and `--model` prints `c no best-so-far assignment` instead of a made-up assignment.

## Measured (2-core cloud VM, release build, 10 s budget, default seed)

| Instance | Result | Time |
|---|---|---|
| random 3-SAT 150 vars, r=4.26 (×2) | UNSAT | 20 ms, 100 ms |
| random 3-SAT 250 vars, r=4.20 | UNKNOWN (best: 1 clause) at 10 s; UNSAT in 13.6 s with 60 s budget | — |
| planted 3-SAT 5k / 50k vars | SAT | 0.26 s / 1.0 s |
| random 3-SAT 100k vars, r=3.9 | SAT | 3.1 s |
| random 3-SAT 120 / 200 vars, r=5.5 / 6.0 | UNSAT | 2.5 ms / 48 ms |
| pigeonhole 8→7 / 9→8 | UNSAT | 40 ms / 3.9 s (seeds 1–10: 0.44–1.35 s, median ≈0.75 s) |

Allocations inside `solve()`: 0 on every run. Self-test: 3,000 brute-force + 300 DPLL-referenced instances, 0 failures; 1,500 + 150 more under each of `--no-relax`, `--no-learning`, `--steepest`, also 0 failures.

## Deviations and honest limits

- **Propositional SAT only.** There is no theory layer (no SMT); the architecture leaves room for one but none is implemented.
- **SLS rule.** The spec's "steepest make−break" rule is implemented (`--steepest`, with PAWS weighting), but the default is a probSAT-style rule P ∝ (1+break)^−2.38 because it measured far better: 100k vars at r=3.9, 3 s of SLS — steepest left 952 clauses violated, probSAT solved it.
- **"Single pool".** Memory is fixed-capacity boxed slices whose exact total is computed and budget-checked before allocation, not one `malloc` carved with unsafe lifetimes. Same predictability, safe Rust.
- **Bounded learnt arena ⇒ completeness is bounded.** Dropping/reducing learnt clauses is always sound, but on adversarial instances the fixed arena can prevent a proof within the budget → UNKNOWN.
- **No UNSAT certificate (DRAT).** UNSAT answers are validated only by tests (brute force, DPLL), not per run.
- **Learning payoff is unproven.** The bandit visibly learns (e.g. SLS dominates on large random SAT, see the Q-table printout), but seed variance on hard instances (PHP 9→8: 0.4–3.9 s) is larger than any learning-vs-round-robin difference I measured; I did not run a statistically meaningful ablation.
- **Anytime overhead on UNSAT.** The Conservative completeness guard only reserves ≥50% of time for CDCL, so pure-UNSAT instances pay up to ~2× versus a CDCL-only solver.
- **`--timeout` is bounded, not exact.** `solve()` returns within `timeout + overshoot`, where the overshoot is at most about one root rebuild + one full evaluation + ~20 ms (the final evaluation may use a grace of `clamp(timeout/20, 5, 50)` ms and is discarded if it cannot finish). Rebuilds (`root_simplify_and_rebuild`, `reduce_db`), `sls_init_state` and the strict re-check after SAT/root conflict are atomic and never interrupted; optional pre/in-processing passes stop at `Config::preprocess_budget_ppm` (15 % of the timeout). On a 2M-var / 8M-clause instance a rebuild is ~0.3 s and an evaluation ~0.1 s here, so `--timeout 100` still takes ~0.4 s; on 300k vars the overshoot is ~20 ms. Details and measurements: `docs/references/deadline-contract.md`.
- Unchecked indexing relies on load-time validation of all literals/ranges; `--features checked` and debug builds (which also verify the watch invariant after every rebuild) are the audit path.
