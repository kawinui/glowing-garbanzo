//! # zsat — a zero-allocation hardened SAT solver
//!
//! All memory is planned and budget-checked in [`SolverWorkspace::new`];
//! [`SolverWorkspace::solve`] never touches the heap.
//!
//! Module map:
//! * `types`, `arena`, `util` — layout, workspace, aligned bit-vectors, PRNG, ticker, log
//! * `propagate` — 2WL propagation over intrusive fixed watch lists, root rebuild
//! * `order` — flat-score segment-tree decision queue with bitwise decay (Module 4)
//! * `cdcl` — bounded CDCL, in-place clause-DB reduction (the UNSAT prover)
//! * `sls` — weighted make/break local search (Module 2)
//! * `lookahead` — failed-literal probing (Module 3)
//! * `preprocess` — UP, pure literals, signature subsumption (Module 6)
//! * `controller` — FSM with hysteresis + Q-table bandit (Module 7)
//! * `solver` — relaxation tiers, anytime best, strict verification (Modules 1, 5)

pub mod arena;
pub mod cdcl;
pub mod controller;
pub mod lookahead;
pub mod order;
pub mod preprocess;
pub mod propagate;
pub mod sls;
pub mod solver;
pub mod types;
pub mod util;

pub use arena::{Formula, LoadError, SolverWorkspace};
pub use types::{Action, Config, Event, EventKind, Lit, Mode, Status, Why};

/// Alias: the workspace *is* the solver.
pub type Solver = SolverWorkspace;
