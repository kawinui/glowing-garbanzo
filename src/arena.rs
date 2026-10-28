//! Memory layout: the input `Formula` (load-time only), the byte-exact
//! `Layout` plan that is checked against the memory budget *before* anything
//! is allocated, and `SolverWorkspace`, which owns every array the search
//! will ever touch. After `SolverWorkspace::new` returns, `solve()` performs
//! zero heap allocations (verified by the counting allocator in `main.rs`).

use crate::controller::{Controller, QTable};
use crate::types::*;
use crate::util::*;
use std::time::Instant;

// ---------------------------------------------------------------------------
// Input formula (CSR, normalized). Allocation here is load time.
// ---------------------------------------------------------------------------

#[derive(Clone, Debug, Default)]
pub struct Formula {
    pub num_vars: u32,
    pub lits: Vec<Lit>,
    /// `starts.len() == num_clauses + 1`
    pub starts: Vec<u32>,
    pub tautologies_dropped: u32,
}

impl Formula {
    pub fn new(num_vars: u32) -> Self {
        Formula { num_vars, lits: Vec::new(), starts: vec![0], tautologies_dropped: 0 }
    }

    #[inline]
    pub fn num_clauses(&self) -> usize {
        self.starts.len() - 1
    }

    #[inline]
    pub fn clause(&self, i: usize) -> &[Lit] {
        &self.lits[self.starts[i] as usize..self.starts[i + 1] as usize]
    }

    /// Add a DIMACS clause: dedups literals, drops tautologies.
    pub fn add_clause(&mut self, dimacs: &[i32]) {
        let mut c: Vec<Lit> = dimacs.iter().filter(|&&d| d != 0).map(|&d| Lit::from_dimacs(d)).collect();
        c.sort_unstable();
        c.dedup();
        if c.windows(2).any(|w| w[0].var() == w[1].var()) {
            self.tautologies_dropped += 1;
            return;
        }
        for l in &c {
            self.num_vars = self.num_vars.max(l.var() + 1);
        }
        self.lits.extend_from_slice(&c);
        self.starts.push(self.lits.len() as u32);
    }

    pub fn parse_dimacs(text: &str) -> Result<Formula, String> {
        let mut f = Formula::new(0);
        let mut cur: Vec<i32> = Vec::new();
        let mut declared = None;
        for (ln, line) in text.lines().enumerate() {
            let t = line.trim();
            if t.is_empty() || t.starts_with('c') {
                continue;
            }
            if t.starts_with('%') {
                break; // SATLIB terminator
            }
            if t.starts_with('p') {
                let p: Vec<&str> = t.split_whitespace().collect();
                if p.len() < 4 || p[1] != "cnf" {
                    return Err(format!("line {}: bad problem line", ln + 1));
                }
                let nv: u32 = p[2].parse().map_err(|_| format!("line {}: bad var count", ln + 1))?;
                let nc: usize = p[3].parse().map_err(|_| format!("line {}: bad clause count", ln + 1))?;
                f.num_vars = nv;
                declared = Some(nc);
                continue;
            }
            for tok in t.split_whitespace() {
                let d: i32 = tok.parse().map_err(|_| format!("line {}: bad literal '{tok}'", ln + 1))?;
                if d == 0 {
                    f.add_clause(&cur);
                    cur.clear();
                } else {
                    if d == i32::MIN {
                        return Err(format!("line {}: literal out of range", ln + 1));
                    }
                    cur.push(d);
                }
            }
        }
        if !cur.is_empty() {
            f.add_clause(&cur);
        }
        let _ = declared;
        Ok(f)
    }
}

// ---------------------------------------------------------------------------
// Memory plan
// ---------------------------------------------------------------------------

#[derive(Copy, Clone, Debug)]
pub struct Layout {
    pub n_vars: usize,
    pub n_orig: usize,
    pub orig_lits: usize,
    pub learnt_lits: usize,
    pub learnt_clauses: usize,
}

impl Layout {
    pub fn tree_leaves(&self) -> usize {
        self.n_vars.max(1).next_power_of_two()
    }

    /// Exact byte count of every array `SolverWorkspace::new` allocates.
    pub fn bytes(&self) -> usize {
        let n = self.n_vars;
        let l = 2 * n;
        let c0 = self.n_orig;
        let a0 = self.orig_lits;
        let cmax = c0 + self.learnt_clauses;
        let p = self.tree_leaves();
        let bv = BitSet::bytes_for(n);
        let bc = BitSet::bytes_for(c0);
        let mut b = 0usize;
        b += 4 * a0 + 4 * (c0 + 1); // pristine copy
        b += 4 * (a0 + self.learnt_lits) + 16 * cmax; // working arena + headers
        b += 8 * 2 * cmax + 4 * l; // watch nodes + heads
        b += l + 4 * n * 3 + 4 * (n + 1); // val, level, reason, trail, trail_lim
        b += n + 4 * (n + 1) * 3; // seen, learnt_buf, clear_buf, level_stamp
        b += 4 * n + 4 * 2 * p; // score, tree
        b += 6 * bv; // phase, best, model, sls_val, sls_best, frozen
        b += 3 * bc; // active, unsat_bits, eval_unsat
        b += 4 * c0 * 2 + n; // masked_list, clause_weight, probe_penalty
        b += 4 * (l + 1) + 4 * a0; // occurrence CSR
        b += 16 * c0 + 4 * c0 + 8 * n * 2 + 4 * n; // SlsClause, unsat_list, make, brk, flip_trail
        b += 4 * l + 8 * c0 + 4 * l; // lit_count, sig, lit_stamp
        b += 2 * EventLog::bytes();
        b += core::mem::size_of::<SolverWorkspace>();
        b
    }
}

#[derive(Debug)]
pub enum LoadError {
    OverBudget { need: usize, budget: usize },
    TooLarge(&'static str),
}

impl core::fmt::Display for LoadError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            LoadError::OverBudget { need, budget } => {
                write!(f, "formula needs {need} bytes, budget is {budget} bytes")
            }
            LoadError::TooLarge(s) => write!(f, "formula too large: {s}"),
        }
    }
}

// ---------------------------------------------------------------------------
// Hot scalar state, one cache line each.
// ---------------------------------------------------------------------------

#[repr(C, align(64))]
#[derive(Clone, Debug, Default)]
pub struct Hot {
    pub trail_len: u32,
    pub qhead: u32,
    pub dlevel: u32,
    pub num_learnt: u32,
    pub learnt_top: u32,
    pub all_active: bool,
    pub hybrid_scoring: bool,
    pub inc: u32,
    pub decay_interval: u32,
    pub since_decay: u32,
    pub luby_idx: u32,
    pub since_restart: u32,
    pub reduce_target: u32,
    pub stamp_gen: u32,
    pub level_gen: u32,
}

#[repr(C, align(64))]
#[derive(Clone, Debug, Default)]
pub struct Stats {
    pub conflicts: u64,
    pub decisions: u64,
    pub propagations: u64,
    pub restarts: u64,
    pub learnt_units: u64,
    pub reductions: u64,
    pub sls_flips: u64,
    pub probes: u64,
    pub failed_lits: u64,
    pub subsumed: u64,
    pub pure: u64,
    pub epochs: u64,
}

// ---------------------------------------------------------------------------
// The workspace
// ---------------------------------------------------------------------------

pub struct SolverWorkspace {
    pub cfg: Config,
    pub layout: Layout,
    pub allocated_bytes: usize,
    pub n_vars: u32,
    pub n_orig: u32,
    pub hot: Hot,
    pub stats: Stats,

    // pristine original clauses (verification + SLS)
    pub(crate) orig_lits: Box<[Lit]>,
    pub(crate) orig_start: Box<[u32]>,

    // working clause DB: originals at [0, A0), learnt region after
    pub(crate) lits: Box<[Lit]>,
    pub(crate) hdr: Box<[ClauseHeader]>,
    pub(crate) learnt_base: u32,
    pub(crate) learnt_clause_cap: u32,

    // watches
    pub(crate) wnode: Box<[WatchNode]>,
    pub(crate) whead: Box<[u32]>,

    // assignment
    pub(crate) val: Box<[i8]>,
    pub(crate) level: Box<[u32]>,
    pub(crate) reason: Box<[u32]>,
    pub(crate) trail: Box<[Lit]>,
    pub(crate) trail_lim: Box<[u32]>,

    // conflict analysis scratch
    pub(crate) seen: Box<[u8]>,
    pub(crate) learnt_buf: Box<[Lit]>,
    pub(crate) clear_buf: Box<[Lit]>,
    pub(crate) level_stamp: Box<[u32]>,

    // variable order (segment tree over flat scores)
    pub(crate) score: Box<[u32]>,
    pub(crate) tree: Box<[u32]>,
    pub(crate) leaves: u32,

    // phases / models
    pub(crate) phase: BitSet,
    pub(crate) best: BitSet,
    pub(crate) model: BitSet,
    pub(crate) sls_val: BitSet,
    pub(crate) sls_best: BitSet,
    pub(crate) frozen: BitSet,

    // relaxation + penalties
    pub(crate) active: BitSet,
    pub(crate) unsat_bits: BitSet,
    pub(crate) eval_unsat: BitSet,
    pub(crate) masked_list: Box<[u32]>,
    pub(crate) num_masked: u32,
    pub(crate) initial_masked: u32,
    pub(crate) relax_k: u32,
    pub(crate) clause_weight: Box<[u32]>,
    pub(crate) probe_penalty: Box<[u8]>,

    // occurrence lists over pristine clauses (CSR)
    pub(crate) occ_start: Box<[u32]>,
    pub(crate) occ: Box<[u32]>,

    // SLS state
    /// Packed per-clause SLS record: one cache miss per touched clause.
    pub(crate) sls_c: Box<[crate::sls::SlsClause]>,
    pub(crate) make: Box<[u64]>,
    pub(crate) brk: Box<[u64]>,
    pub(crate) unsat_list: Box<[u32]>,
    pub(crate) unsat_len: u32,
    /// Vars flipped since the last best snapshot (lazy best-copy).
    pub(crate) flip_trail: Box<[u32]>,
    /// SLS state is resumable while root facts and masks are unchanged.
    pub(crate) sls_ready: bool,
    pub(crate) sls_root_len: u32,
    pub(crate) sls_masked: u32,
    pub(crate) sls_tracks_make: bool,
    pub(crate) prob_tab: [f32; 256],

    // preprocessing scratch
    pub(crate) lit_count: Box<[u32]>,
    pub(crate) sig: Box<[u64]>,
    pub(crate) lit_stamp: Box<[u32]>,

    // control
    pub(crate) rng: Rng,
    pub ctrl: Controller,
    pub q: QTable,
    pub log: EventLog,
    /// Mode transitions only (never crowded out by per-epoch events).
    pub mode_log: EventLog,
    pub best_unsat: u32,
    pub(crate) t0: Instant,
    pub(crate) epoch: u32,
}

impl SolverWorkspace {
    /// Plan, budget-check, allocate and load. The only place that allocates.
    pub fn new(f: &Formula, cfg: Config) -> Result<Self, LoadError> {
        let n = f.num_vars as usize;
        let c0 = f.num_clauses();
        let a0 = f.lits.len();
        if n >= (1usize << 30) {
            return Err(LoadError::TooLarge("variables"));
        }
        if a0 >= (1usize << 31) {
            return Err(LoadError::TooLarge("literals"));
        }
        // Size the learnt arena, shrinking it until the whole plan fits.
        let mut ll = (a0.saturating_mul(cfg.learnt_lit_factor)).max(cfg.min_learnt_lits).min((1usize << 31) - a0 - 1);
        let min_ll = (4 * n + 1024).min(ll);
        let mk = |ll: usize| Layout {
            n_vars: n,
            n_orig: c0,
            orig_lits: a0,
            learnt_lits: ll,
            learnt_clauses: (ll / 4).max(64),
        };
        let mut layout = mk(ll);
        while layout.bytes() > cfg.memory_budget && ll > min_ll {
            ll = (ll / 2).max(min_ll);
            layout = mk(ll);
        }
        if layout.bytes() > cfg.memory_budget {
            return Err(LoadError::OverBudget { need: layout.bytes(), budget: cfg.memory_budget });
        }
        let cmax = c0 + layout.learnt_clauses;
        if cmax >= (1usize << 31) {
            return Err(LoadError::TooLarge("clauses"));
        }
        let l2 = 2 * n;
        let p = layout.tree_leaves();

        // ---- allocate everything (load time) ----
        let mut ws = SolverWorkspace {
            cfg,
            layout,
            allocated_bytes: layout.bytes(),
            n_vars: n as u32,
            n_orig: c0 as u32,
            hot: Hot::default(),
            stats: Stats::default(),
            orig_lits: f.lits.clone().into_boxed_slice(),
            orig_start: f.starts.clone().into_boxed_slice(),
            lits: boxed(a0 + ll, Lit(0)),
            hdr: boxed(cmax, ClauseHeader::default()),
            learnt_base: a0 as u32,
            learnt_clause_cap: layout.learnt_clauses as u32,
            wnode: boxed(2 * cmax, WatchNode { next: NIL, blocker: Lit(0) }),
            whead: boxed(l2, NIL),
            val: boxed(l2, V_UNDEF),
            level: boxed(n, 0),
            reason: boxed(n, NIL),
            trail: boxed(n, Lit(0)),
            trail_lim: boxed(n + 1, 0),
            seen: boxed(n, 0),
            learnt_buf: boxed(n + 1, Lit(0)),
            clear_buf: boxed(n + 1, Lit(0)),
            level_stamp: boxed(n + 1, 0),
            score: boxed(n, 0),
            tree: boxed(2 * p, NIL),
            leaves: p as u32,
            phase: BitSet::new(n),
            best: BitSet::new(n),
            model: BitSet::new(n),
            sls_val: BitSet::new(n),
            sls_best: BitSet::new(n),
            frozen: BitSet::new(n),
            active: BitSet::new(c0),
            unsat_bits: BitSet::new(c0),
            eval_unsat: BitSet::new(c0),
            masked_list: boxed(c0, 0),
            num_masked: 0,
            initial_masked: 0,
            relax_k: 0,
            clause_weight: boxed(c0, 1),
            probe_penalty: boxed(n, 0),
            occ_start: boxed(l2 + 1, 0),
            occ: boxed(a0, 0),
            sls_c: boxed(c0, crate::sls::SlsClause::default()),
            make: boxed(n, 0),
            brk: boxed(n, 0),
            unsat_list: boxed(c0, 0),
            unsat_len: 0,
            flip_trail: boxed(n, 0),
            sls_ready: false,
            sls_root_len: 0,
            sls_masked: 0,
            sls_tracks_make: false,
            prob_tab: crate::sls::prob_table(),
            lit_count: boxed(l2, 0),
            sig: boxed(c0, 0),
            lit_stamp: boxed(l2, 0),
            rng: Rng::new(cfg.seed),
            ctrl: Controller::new(),
            q: QTable::new(),
            log: EventLog::new(),
            mode_log: EventLog::new(),
            best_unsat: u32::MAX,
            t0: Instant::now(),
            epoch: 0,
        };

        // ---- load clauses into the working arena ----
        ws.lits[..a0].copy_from_slice(&f.lits);
        for c in 0..c0 {
            let s = f.starts[c];
            let e = f.starts[c + 1];
            ws.hdr[c] = ClauseHeader { start: s, len: e - s, lbd: 0, flags: 0, birth: 0 };
        }
        // validate the unchecked-index invariant once
        assert!(f.lits.iter().all(|l| (l.idx()) < l2), "literal out of range");

        // ---- occurrence CSR ----
        for l in f.lits.iter() {
            ws.occ_start[l.idx() + 1] += 1;
        }
        for i in 0..l2 {
            ws.occ_start[i + 1] += ws.occ_start[i];
        }
        {
            let mut fill: Vec<u32> = ws.occ_start[..l2].to_vec(); // load-time temp
            for c in 0..c0 {
                for k in f.starts[c]..f.starts[c + 1] {
                    let l = f.lits[k as usize];
                    ws.occ[fill[l.idx()] as usize] = c as u32;
                    fill[l.idx()] += 1;
                }
            }
        }

        ws.active.set_all();
        ws.hot.all_active = true;
        ws.hot.learnt_top = a0 as u32;
        ws.hot.inc = 1;
        ws.hot.decay_interval = crate::controller::PARAMS[0].decay_interval;
        ws.hot.reduce_target = 2_000u32.min(ws.learnt_clause_cap * 3 / 4).max(16);
        ws.hot.stamp_gen = 0;
        ws.order_init();
        Ok(ws)
    }

    // ---- accessors for harness ----

    pub fn num_vars(&self) -> u32 {
        self.n_vars
    }
    pub fn num_clauses(&self) -> u32 {
        self.n_orig
    }
    /// Verified model (valid after `Status::Sat`).
    pub fn model_value(&self, v: Var) -> bool {
        self.model.get(v as usize)
    }
    /// Anytime best assignment (valid after any result).
    pub fn best_value(&self, v: Var) -> bool {
        self.best.get(v as usize)
    }
    pub fn elapsed_us(&self) -> u64 {
        self.t0.elapsed().as_micros() as u64
    }
    #[inline]
    pub(crate) fn emit(&mut self, kind: EventKind) {
        let e = Event { t_us: self.t0.elapsed().as_micros() as u64, epoch: self.epoch, kind };
        self.log.push(e);
    }
    #[inline(always)]
    pub(crate) fn orig_range(&self, c: usize) -> (usize, usize) {
        (at(&self.orig_start, c) as usize, at(&self.orig_start, c + 1) as usize)
    }
    #[inline(always)]
    pub(crate) fn occ_range(&self, l: Lit) -> (usize, usize) {
        (at(&self.occ_start, l.idx()) as usize, at(&self.occ_start, l.idx() + 1) as usize)
    }
    /// Next stamp generation for `lit_stamp` (wraps safely).
    #[inline]
    pub(crate) fn next_stamp(&mut self) -> u32 {
        if self.hot.stamp_gen == u32::MAX {
            self.lit_stamp.fill(0);
            self.hot.stamp_gen = 0;
        }
        self.hot.stamp_gen += 1;
        self.hot.stamp_gen
    }
}
