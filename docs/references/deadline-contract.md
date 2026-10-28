# Deadline contract

`solve()` returns within `timeout_ms + overshoot`, where the overshoot is bounded
by the **unstoppable units** below, not by how big the instance is. The deadline
(`SolverWorkspace::deadline`) is set from `Config::timeout_ms` at the top of
`solve()`; nothing reads the clock inside `propagate()`.

## Atomic vs stoppable work

| Work | Class | Why / how it stops |
|---|---|---|
| `root_simplify_and_rebuild()` | **atomic** | After `whead.fill(NIL)` the watches are gone until the loop ends. Never interrupted; optional callers simply do not *start* it past the deadline. The first one (in `preprocess`) is mandatory: it builds every watch. |
| `reduce_db()` | **atomic** | In-place compaction + rebuild. |
| `unmask_all()`'s rebuild | **atomic** | Mandatory once an FSM transition to Conservative has begun. |
| `verify_model_strict()` | **never cut** | Runs `eval_into` to completion; `Sat` is only returned after it. |
| `sls_init_state()` | **atomic** | O(literals) rebuild of `sls_c`/`brk`/`make`/unsat list. A half-built state would corrupt break counts, so it is not interruptible; SLS restarts are not begun past the deadline. |
| `pure_literal_pass(deadline)` | stoppable *while counting* | Past the deadline during the count phase it returns 0 having enqueued nothing. Once enqueueing starts it finishes, and the caller must rebuild (it always does). |
| `subsumption_pass(budget, deadline)` | stoppable | Checks every 1024 outer clauses. A clause is flagged deleted only after it is proven subsumed, so stopping early only deletes fewer. |
| `eval_into_by(.., deadline)` | stoppable | Checks every 8192 clauses, returns `None`. `assemble_and_eval` then leaves `best` / `best_unsat` untouched, so `violated(best) == best_unsat` always holds. |
| `cdcl_burst`, `probe` | stoppable | `Ticker::tick_n(1 + Δpropagations/64)`: cost-aware, so a conflict that propagates 10^5 literals ends the burst promptly. |
| `inprocess()` | optional | Not started past the deadline; its pure/subsumption passes stop at `min(deadline, start + preprocess budget)`. |

## Budgets

* **Preprocess budget** — `Config::preprocess_budget_ppm` (default 150 000 = 15 % of
  `timeout_ms`). `preprocess` and `inprocess` skip the pure pass, subsumption and
  round 2 once it is spent (logged as `EventKind::Skipped`). On the 2M-var instance
  subsumption alone used to burn ~5 s and removed 0 clauses.
* **Grace** — `clamp(timeout_ms / 20, 5, 50)` ms. After the deadline, only the final
  evaluation of the epoch's assignment may run, bounded by `deadline + grace`; if it
  cannot finish it is discarded. The main loop then breaks without `tighten`, FSM
  transition or in-processing.
* **Overshoot bound** — at most one rebuild + one eval + ~20 ms
  (`--deadline-check` measures both units on the machine and uses exactly this limit).
  Unstoppable tails: a `tighten` / FSM `unmask_all` / `inprocess` rebuild that began
  just before the deadline, `sls_init_state`, and the strict re-check after a `Sat`
  or root conflict.

## UNKNOWN is reported honestly

`has_best()` is `best_unsat != u32::MAX`. With no evaluated assignment the harness
prints `no assignment evaluated within budget` (not the sentinel), `--model` prints
`c no best-so-far assignment`, and `--bench` shows `-`.

## Measured (release, 4-vCPU cloud VM; ms)

`mid` = 300k vars / 1.2M clauses (r=4.0); `big` = 2M vars / 8M clauses (`--mem 2048`).
This machine is ~2× slower than the machine the targets were set on; one rebuild /
one eval cost 19–33 / 14–18 ms on mid and 280–370 / 110–117 ms on big.

| Instance | timeout | before (2 runs) | after (3 runs) | planner target |
|---|---|---|---|---|
| big | 50 | 10 592, 10 001 | 525, 413, 408 | — |
| big | 100 | 9 233, 10 486 | 359, 389, 417 | ≤ 450 |
| big | 1000 | 10 922, 10 792 | 1 003, 1 050, 1 050 | ≤ 1 150 |
| mid | 50 | 1 131, 804 | 77, 75, 63 | ≤ 120 |
| mid | 100 | 891, 811 | 111, 124, 117 | — |
| mid | 1000 | 1 166, 1 457 | 1 020, 1 024, 1 024 | ≤ 1 060 |

Reproduce: `cargo build --release && ./target/release/zsat --deadline-check`
(exit 1 if any row exceeds `timeout + rebuild + eval + 20 ms`, allocates, or reports
an inconsistent best).
