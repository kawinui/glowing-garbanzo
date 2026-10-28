//! Compact core representations: literals, clause headers, watch nodes,
//! solver modes/actions and the fixed-size event record used by the log.
//!
//! Everything here is `Copy` and heap-free so it can live inside the
//! pre-allocated arenas and be moved around inside the search loop for free.

use core::ops::Not;

/// Variable index (0-based internally, DIMACS `v` maps to `v-1`).
pub type Var = u32;

/// Universal "null index" for clause ids, watch-node links and tree leaves.
pub const NIL: u32 = u32::MAX;

/// Literal packed as `var << 1 | sign`. `!lit` is a single XOR.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Default)]
#[repr(transparent)]
pub struct Lit(pub u32);

impl Lit {
    /// Sentinel. Its `var()` (0x7FFF_FFFF) can never collide with a real variable
    /// because the loader rejects formulas with that many variables.
    pub const UNDEF: Lit = Lit(u32::MAX);

    #[inline(always)]
    pub const fn new(v: Var, negative: bool) -> Self {
        Lit((v << 1) | negative as u32)
    }
    #[inline(always)]
    pub const fn var(self) -> Var {
        self.0 >> 1
    }
    #[inline(always)]
    pub const fn is_neg(self) -> bool {
        self.0 & 1 == 1
    }
    #[inline(always)]
    pub const fn idx(self) -> usize {
        self.0 as usize
    }
    pub fn from_dimacs(d: i32) -> Self {
        debug_assert!(d != 0);
        Lit::new(d.unsigned_abs() - 1, d < 0)
    }
    pub fn to_dimacs(self) -> i64 {
        let v = self.var() as i64 + 1;
        if self.is_neg() {
            -v
        } else {
            v
        }
    }
}

impl Not for Lit {
    type Output = Lit;
    #[inline(always)]
    fn not(self) -> Lit {
        Lit(self.0 ^ 1)
    }
}

/// Literal-indexed truth values (`val[lit]`): branch-free lookup in propagation.
pub const V_TRUE: i8 = 1;
pub const V_FALSE: i8 = -1;
pub const V_UNDEF: i8 = 0;

/// Clause flags.
pub const F_LEARNT: u16 = 1;
pub const F_DELETED: u16 = 2;

/// 16-byte clause header: four per cache line. Literals live in the flat arena
/// at `lits[start .. start+len]`; for watched clauses positions 0 and 1 are the
/// two watched literals.
#[repr(C)]
#[derive(Copy, Clone, Default, Debug)]
pub struct ClauseHeader {
    pub start: u32,
    pub len: u32,
    pub lbd: u16,
    pub flags: u16,
    /// Conflict index at which a learnt clause was born (age tie-break).
    pub birth: u32,
}
const _: () = assert!(core::mem::size_of::<ClauseHeader>() == 16);

/// Intrusive watch-list node. Node `2c + w` watches `lits[start(c) + w]`.
/// The total node count is fixed (2 per clause slot), so moving a watch is an
/// O(1) unlink/relink and can never allocate.
#[repr(C)]
#[derive(Copy, Clone, Debug)]
pub struct WatchNode {
    pub next: u32,
    pub blocker: Lit,
}
const _: () = assert!(core::mem::size_of::<WatchNode>() == 8);

/// Final verdict.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum Status {
    Sat,
    Unsat,
    Unknown,
}

/// Controller FSM state.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
#[repr(u8)]
pub enum Mode {
    Aggressive = 0,
    Balanced = 1,
    Conservative = 2,
}

impl Mode {
    #[inline(always)]
    pub const fn idx(self) -> usize {
        self as usize
    }
    pub const fn name(self) -> &'static str {
        match self {
            Mode::Aggressive => "Aggressive",
            Mode::Balanced => "Balanced",
            Mode::Conservative => "Conservative",
        }
    }
}

/// Why a mode transition happened (logged).
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum Why {
    SteadyProgress,
    Stagnation,
    NearSolution,
    TimePressure,
    RelaxExhausted,
    ProofEscalation,
    ModelVerification,
    EscapeStall,
}

/// Discrete operator space for the bandit.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
#[repr(u8)]
pub enum Action {
    Sls = 0,
    Probe = 1,
    Tighten = 2,
    SwitchScoring = 3,
    CdclBestPhase = 4,
    CdclRandomPhase = 5,
}
pub const NUM_ACTIONS: usize = 6;

impl Action {
    pub const ALL: [Action; NUM_ACTIONS] = [
        Action::Sls,
        Action::Probe,
        Action::Tighten,
        Action::SwitchScoring,
        Action::CdclBestPhase,
        Action::CdclRandomPhase,
    ];
    #[inline(always)]
    pub const fn idx(self) -> usize {
        self as usize
    }
    #[inline(always)]
    pub const fn is_cdcl(self) -> bool {
        matches!(
            self,
            Action::SwitchScoring | Action::CdclBestPhase | Action::CdclRandomPhase
        )
    }
    pub const fn name(self) -> &'static str {
        match self {
            Action::Sls => "SLS",
            Action::Probe => "Probe",
            Action::Tighten => "Tighten",
            Action::SwitchScoring => "SwitchScore+CDCL",
            Action::CdclBestPhase => "CDCL(best-phase)",
            Action::CdclRandomPhase => "CDCL(rand-phase)",
        }
    }
}

/// Optional work skipped because a deadline had already passed (logged).
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum Skip {
    PurePass,
    Subsumption,
    PreprocessRound,
    Inprocess,
}

/// Fixed-size log record — no strings, no heap.
#[derive(Copy, Clone, Debug)]
pub enum EventKind {
    Preprocess { fixed: u32, subsumed: u32, pure: u32 },
    Masked { masked: u32, k: u32 },
    Mode { from: Mode, to: Mode, why: Why },
    Action { action: Action, reward: f32, best_unsat: u32, mode: Mode },
    Tighten { k: u32, masked: u32 },
    NewBest { unsat: u32 },
    RelaxedRootConflict,
    Reduce { kept: u32, deleted: u32 },
    Probe { fixed: u32, failed: u32 },
    Verified { sat: bool, unsat_clauses: u32 },
    Skipped { what: Skip },
    Timeout,
}

#[derive(Copy, Clone, Debug)]
pub struct Event {
    pub t_us: u64,
    pub epoch: u32,
    pub kind: EventKind,
}

/// Tuning + budgets. All bounds are applied at load time.
#[derive(Copy, Clone, Debug)]
pub struct Config {
    /// Global wall-clock budget.
    pub timeout_ms: u64,
    /// Hard cap on the bytes the workspace may allocate (checked before allocating).
    pub memory_budget: usize,
    pub seed: u64,
    /// Learnt-literal arena = factor × original literals (shrunk to fit the budget).
    pub learnt_lit_factor: usize,
    pub min_learnt_lits: usize,
    /// Fraction (ppm) of clauses masked out at the start of Aggressive mode.
    pub initial_mask_ppm: u32,
    /// Initial relaxation `k` as ppm of clause count (min 1).
    pub initial_k_ppm: u32,
    /// Enable the Q-learning selector (false = fixed round-robin policy, for ablation).
    pub learning: bool,
    /// Enable progressive relaxation (false = strict from the start).
    pub relaxation: bool,
    /// SLS flip rule.
    pub sls_rule: SlsRule,
    /// Optional pre-/in-processing passes (pure literals, subsumption) stop
    /// once this share of `timeout_ms` (ppm) has elapsed since the start of
    /// `solve()` (pre-) or of the pass (in-). The first root rebuild is mandatory.
    pub preprocess_budget_ppm: u32,
}

/// Local-search variable selection inside a random unsat clause.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum SlsRule {
    /// Freebie, else flip with probability ∝ (1 + break)^-2.38 (probSAT-poly):
    /// a softened steepest descent on the break term. Default — it wins
    /// decisively on random/structured k-SAT in our benchmarks.
    ProbSat,
    /// Freebie, else adaptive-noise random walk, else steepest weighted
    /// `make − break` with PAWS clause weighting at local minima.
    Steepest,
}

impl Default for Config {
    fn default() -> Self {
        Config {
            timeout_ms: 10_000,
            memory_budget: 512 << 20,
            seed: 0x5EED_1234_ABCD_0001,
            learnt_lit_factor: 6,
            min_learnt_lits: 1 << 20,
            initial_mask_ppm: 150_000,
            initial_k_ppm: 20_000,
            learning: true,
            relaxation: true,
            sls_rule: SlsRule::ProbSat,
            preprocess_budget_ppm: 150_000,
        }
    }
}
