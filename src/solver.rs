//! The anytime solving loop: Module 1 (progressive relaxation + safety
//! switch), Module 5 (multi-seed short runs + anytime best tracker) and the
//! glue that runs Module 7's FSM + bandit over the engines.
//!
//! Soundness contract:
//! * `Sat` is returned only after the controller is in Conservative mode with
//!   100% of clauses active, `k == 0`, and the candidate model evaluates to
//!   0 violated clauses against the *pristine* (never simplified) clause copy.
//! * `Unsat` is returned only after a level-0 conflict has been derived and
//!   the solver has been escalated to Conservative / 100% active / `k == 0`.
//!   Every root fact and learnt clause is an implication of a *subset* of the
//!   original clauses (or a satisfiability-preserving pure-literal step), so
//!   a root conflict found in any tier is a refutation of the full formula;
//!   the escalation then re-checks it in strict mode.
//! * Otherwise `Unknown`, with the best assignment in `best` and its
//!   violated-clause count in `best_unsat`.

use crate::arena::SolverWorkspace;
use crate::cdcl::Burst;
use crate::controller::{reward, Observation, PARAMS};
use crate::propagate::Root;
use crate::sls::SlsStart;
use crate::types::*;
use crate::util::*;
use std::time::{Duration, Instant};

const TRANSITION_PENALTY: u32 = 4;

#[derive(Copy, Clone, Default, Debug)]
struct ActionResult {
    root_conflict: bool,
    sat_model: bool,
    target_reached: bool,
}

/// Count clauses of the pristine formula falsified by `assign` into `out`
/// (one bit per clause) and return the hardware popcount.
fn eval_into(lits: &[Lit], starts: &[u32], assign: &BitSet, out: &mut BitSet) -> u32 {
    out.clear_all();
    let nc = starts.len() - 1;
    for c in 0..nc {
        let s = at(starts, c) as usize;
        let e = at(starts, c + 1) as usize;
        let mut sat = false;
        for k in s..e {
            let l = at(lits, k);
            if assign.get(l.var() as usize) != l.is_neg() {
                sat = true;
                break;
            }
        }
        if !sat {
            out.set(c);
        }
    }
    out.count_ones()
}

impl SolverWorkspace {
    #[inline]
    pub(crate) fn relax_exhausted(&self) -> bool {
        self.num_masked == 0 && self.relax_k == 0
    }

    /// Strict = Conservative mode, 100% of clauses active, k == 0.
    #[inline]
    pub fn is_strict(&self) -> bool {
        self.ctrl.mode == Mode::Conservative && self.hot.all_active && self.num_masked == 0 && self.relax_k == 0
    }

    fn k_for(&self, mode: Mode) -> u32 {
        let ppm = PARAMS[mode.idx()].k_ppm as u64;
        if ppm == 0 || !self.cfg.relaxation {
            0
        } else {
            ((self.n_orig as u64 * ppm / 1_000_000) as u32).max(1)
        }
    }

    fn emit_mode(&mut self, t: (Mode, Mode, Why)) {
        let kind = EventKind::Mode { from: t.0, to: t.1, why: t.2 };
        self.emit(kind);
        let e = Event { t_us: self.elapsed_us(), epoch: self.epoch, kind };
        self.mode_log.push(e);
    }

    // ---------------- Module 1: relaxation ----------------

    fn initial_mask(&mut self) {
        self.num_masked = 0;
        if !self.cfg.relaxation {
            return;
        }
        let p = self.cfg.initial_mask_ppm as f32 / 1e6;
        for c in 0..self.n_orig as usize {
            let h = at(&self.hdr, c);
            if h.flags & F_DELETED == 0 && h.len >= 2 && self.rng.chance(p) {
                self.active.clear(c);
                *at_mut(&mut self.masked_list, self.num_masked as usize) = c as u32;
                self.num_masked += 1;
            }
        }
        self.initial_masked = self.num_masked;
        self.hot.all_active = self.num_masked == 0;
        self.relax_k = self.k_for(Mode::Aggressive);
        self.emit(EventKind::Masked { masked: self.num_masked, k: self.relax_k });
    }

    /// Unmask the `m` masked clauses with the highest penalty weight
    /// (log2 histogram threshold + in-place swap-remove; no sort, no alloc).
    fn unmask_top(&mut self, m: u32) {
        let mut hist = [0u32; 33];
        for i in 0..self.num_masked as usize {
            let w = at(&self.clause_weight, at(&self.masked_list, i) as usize).max(1);
            hist[(32 - w.leading_zeros()) as usize] += 1;
        }
        let mut thr = 0usize;
        let mut quota = m;
        let mut acc = 0u32;
        for b in (1..=32).rev() {
            if acc + hist[b] >= m {
                thr = b;
                quota = m - acc;
                break;
            }
            acc += hist[b];
        }
        let mut i = 0usize;
        while i < self.num_masked as usize {
            let c = at(&self.masked_list, i);
            let b = (32 - at(&self.clause_weight, c as usize).max(1).leading_zeros()) as usize;
            let take = b > thr || (b == thr && quota > 0);
            if take {
                if b == thr {
                    quota -= 1;
                }
                self.active.set(c as usize);
                self.num_masked -= 1;
                let last = at(&self.masked_list, self.num_masked as usize);
                *at_mut(&mut self.masked_list, i) = last;
            } else {
                i += 1;
            }
        }
        self.hot.all_active = self.num_masked == 0;
    }

    /// Iterative strengthening: halve k and unmask 15% of the disabled clauses.
    fn tighten(&mut self, penalize: bool) -> Root {
        if penalize {
            // clauses still violated at a relaxation transition get heavier
            for c in 0..self.n_orig as usize {
                if self.eval_unsat.get(c) {
                    let w = at_mut(&mut self.clause_weight, c);
                    *w = (*w + TRANSITION_PENALTY).min(1 << 20);
                }
            }
        }
        self.relax_k >>= 1;
        let mut r = Root::Ok;
        if self.num_masked > 0 {
            let m = (self.num_masked * 15 / 100).max(self.initial_masked / 20).max(1).min(self.num_masked);
            self.unmask_top(m);
            self.backtrack(0);
            r = self.root_simplify_and_rebuild();
        }
        self.emit(EventKind::Tighten { k: self.relax_k, masked: self.num_masked });
        r
    }

    /// Safety switch: go fully strict (100% clauses, k = 0).
    fn unmask_all(&mut self) -> Root {
        for i in 0..self.num_masked as usize {
            let c = at(&self.masked_list, i) as usize;
            self.active.set(c);
        }
        let changed = self.num_masked > 0;
        self.num_masked = 0;
        self.relax_k = 0;
        self.hot.all_active = true;
        self.backtrack(0);
        if changed {
            self.emit(EventKind::Tighten { k: 0, masked: 0 });
        }
        self.root_simplify_and_rebuild()
    }

    fn apply_mode(&mut self) {
        let p = &PARAMS[self.ctrl.mode.idx()];
        self.hot.decay_interval = p.decay_interval;
        self.relax_k = self.relax_k.min(self.k_for(self.ctrl.mode));
    }

    /// A level-0 conflict was derived. Escalate to strict and confirm.
    fn on_root_conflict(&mut self) -> Status {
        if !self.is_strict() {
            self.emit(EventKind::RelaxedRootConflict);
            if let Some(t) = self.ctrl.force(Mode::Conservative, Why::ProofEscalation) {
                self.emit_mode(t);
            }
            self.apply_mode();
            let _ = self.unmask_all(); // re-check in strict mode (derivation is already sound)
        }
        debug_assert!(self.is_strict());
        self.emit(EventKind::Verified { sat: false, unsat_clauses: 0 });
        Status::Unsat
    }

    // ---------------- Module 5: anytime tracker + verification ----------------

    /// Copy `src` (phase or model) into `model`, override root facts, evaluate
    /// against the pristine formula, update the anytime best. Returns #unsat.
    fn assemble_and_eval(&mut self, from_model: bool) -> u32 {
        if !from_model {
            self.model.copy_from(&self.phase);
        }
        for i in 0..self.root_len() as usize {
            let l = at(&self.trail, i);
            self.model.assign(l.var() as usize, !l.is_neg());
        }
        let u = eval_into(&self.orig_lits, &self.orig_start, &self.model, &mut self.eval_unsat);
        if u < self.best_unsat {
            self.best_unsat = u;
            self.best.copy_from(&self.model);
            self.emit(EventKind::NewBest { unsat: u });
        }
        u
    }

    /// Strict verification of `model`. On success the solver is Conservative/100%.
    fn verify_model_strict(&mut self) -> bool {
        if let Some(t) = self.ctrl.force(Mode::Conservative, Why::ModelVerification) {
            self.emit_mode(t);
        }
        self.apply_mode();
        // go strict without disturbing the model
        for i in 0..self.num_masked as usize {
            let c = at(&self.masked_list, i) as usize;
            self.active.set(c);
        }
        self.num_masked = 0;
        self.relax_k = 0;
        self.hot.all_active = true;
        debug_assert!(self.is_strict());
        let u = eval_into(&self.orig_lits, &self.orig_start, &self.model, &mut self.eval_unsat);
        let ok = u == 0 && self.eval_unsat.count_ones() == 0;
        self.emit(EventKind::Verified { sat: ok, unsat_clauses: u });
        ok
    }

    // ---------------- actions ----------------

    fn allowed_actions(&self) -> u32 {
        let mut m = (1u32 << NUM_ACTIONS) - 1;
        if self.relax_exhausted() {
            m &= !(1 << Action::Tighten.idx());
        }
        m
    }

    fn run_cdcl(&mut self, ticker: &mut Ticker, r: &mut ActionResult) {
        match self.cdcl_burst(u64::MAX, ticker) {
            Burst::Sat => r.sat_model = true,
            Burst::RootConflict => r.root_conflict = true,
            Burst::Budget => {}
        }
    }

    fn run_action(&mut self, a: Action, ticker: &mut Ticker) -> ActionResult {
        let mut r = ActionResult::default();
        match a {
            Action::Sls => {
                // relaxed tiers accept up to k violated active clauses
                let target = self.relax_k;
                let noise = self.ctrl.params().sls_noise;
                let try_flips = (self.layout.orig_lits as u64 * 4).max(50_000);
                let mut first = true;
                loop {
                    // multi-seed short runs
                    let start = if first {
                        SlsStart::Resume
                    } else {
                        match self.rng.below(4) {
                            0 => SlsStart::Random,
                            1 => SlsStart::Phase,
                            _ => SlsStart::Best,
                        }
                    };
                    first = false;
                    let o = self.sls_run(start, target, try_flips, noise, ticker);
                    // phase handoff: warm-start CDCL polarities
                    self.phase.copy_from(&self.sls_best);
                    let u = self.assemble_and_eval(false);
                    if u == 0 {
                        r.sat_model = true;
                        break;
                    }
                    if o.reached_target {
                        r.target_reached = true;
                        break;
                    }
                    if ticker.expired {
                        break;
                    }
                }
            }
            Action::Probe => {
                let budget = (self.layout.orig_lits as u64 * 2).max(100_000);
                let o = self.probe(budget, ticker);
                self.emit(EventKind::Probe { fixed: o.fixed, failed: o.failed });
                r.root_conflict = o.root == Root::Conflict || (o.fixed > 0 && self.inprocess() == Root::Conflict);
            }
            Action::Tighten => {
                if self.tighten(false) == Root::Conflict {
                    r.root_conflict = true;
                }
            }
            Action::SwitchScoring => {
                self.hot.hybrid_scoring = !self.hot.hybrid_scoring;
                if self.hot.hybrid_scoring && self.best_unsat != u32::MAX {
                    // inject SLS knowledge: variables of clauses violated by the best assignment
                    let _ = eval_into(&self.orig_lits, &self.orig_start, &self.best, &mut self.eval_unsat);
                    let inc = self.hot.inc.max(1);
                    for c in 0..self.n_orig as usize {
                        if self.eval_unsat.get(c) {
                            let (s, e) = self.orig_range(c);
                            for k in s..e {
                                let v = at(&self.orig_lits, k).var();
                                self.bump_raw(v, inc);
                            }
                        }
                    }
                    self.order_rebuild();
                }
                self.run_cdcl(ticker, &mut r);
            }
            Action::CdclBestPhase => {
                if self.best_unsat != u32::MAX {
                    self.phase.copy_from(&self.best);
                }
                self.run_cdcl(ticker, &mut r);
            }
            Action::CdclRandomPhase => {
                self.phase.fill_random(&mut self.rng);
                self.perturb_scores();
                self.run_cdcl(ticker, &mut r);
            }
        }
        r
    }

    // ---------------- main loop ----------------

    /// Solve. Performs zero heap allocations.
    pub fn solve(&mut self) -> Status {
        self.t0 = Instant::now();
        let global_end = self.t0 + Duration::from_millis(self.cfg.timeout_ms);
        self.log.clear();
        self.mode_log.clear();

        // Preprocessing runs strict (everything active) — Module 6.
        let (r, st) = self.preprocess(2);
        self.emit(EventKind::Preprocess { fixed: st.fixed, subsumed: st.subsumed, pure: st.pure });
        if r == Root::Conflict {
            if let Some(t) = self.ctrl.force(Mode::Conservative, Why::ProofEscalation) {
                self.emit_mode(t);
            }
            return self.on_root_conflict();
        }

        self.initial_mask();
        self.apply_mode();
        let mut ema_work = 0f64;

        loop {
            let now = Instant::now();
            if now >= global_end {
                break;
            }
            self.epoch += 1;
            self.stats.epochs += 1;
            let remaining = (global_end - now).as_millis() as u64;
            let s = self.ctrl.context();
            let allowed = self.allowed_actions();
            let cdcl_mask = (1 << Action::SwitchScoring.idx())
                | (1 << Action::CdclBestPhase.idx())
                | (1 << Action::CdclRandomPhase.idx());
            let a = if self.epoch == 1 {
                Action::Sls // initial rapid SLS pass (Module 2)
            } else if self.ctrl.must_force_cdcl() {
                self.q.best_in(s, cdcl_mask)
            } else {
                self.q.select(s, allowed, &mut self.rng, self.cfg.learning)
            };
            let micro = self.ctrl.micro_ms(remaining);
            let end = (now + Duration::from_millis(micro)).min(global_end);
            let mut ticker = Ticker::new(end, 128);

            let best_before = self.best_unsat;
            let root_before = self.root_len();
            let work_before = self.stats.propagations + self.stats.sls_flips;

            let ar = self.run_action(a, &mut ticker);

            if ar.root_conflict {
                return self.on_root_conflict();
            }
            if ar.sat_model {
                self.assemble_and_eval(true);
            } else if a != Action::Sls {
                // CDCL / probing: evaluate the saved-phase assignment
                self.assemble_and_eval(false);
            }
            if self.best_unsat == 0 {
                self.model.copy_from(&self.best);
                if self.verify_model_strict() {
                    return Status::Sat;
                }
            }

            // ---- reward + Q update (Module 7) ----
            let improved = self.best_unsat < best_before;
            let d_unsat = if best_before == u32::MAX {
                if self.best_unsat != u32::MAX { 1.0 } else { 0.0 }
            } else {
                (best_before - self.best_unsat) as f32 / best_before.max(1) as f32
            };
            let root_after = self.root_len();
            let free = (self.n_vars - root_before).max(1);
            let d_root = ((root_after - root_before) as f32 / free as f32 * 10.0).min(1.0);
            let work = (self.stats.propagations + self.stats.sls_flips - work_before) as f64;
            let cost = if ema_work > 0.0 { (work / ema_work).min(3.0) as f32 } else { 1.0 };
            ema_work = if ema_work == 0.0 { work.max(1.0) } else { 0.9 * ema_work + 0.1 * work };
            let rw = reward(d_unsat, d_root, cost);
            self.q.update(s, a, rw);
            let mode = self.ctrl.mode;
            self.emit(EventKind::Action { action: a, reward: rw, best_unsat: self.best_unsat, mode });
            self.ctrl.account(a.is_cdcl(), (Instant::now() - now).as_micros() as u64);

            // ---- iterative strengthening (Module 1) ----
            if !self.relax_exhausted()
                && (ar.target_reached || (!improved && ticker.expired))
                && self.tighten(ar.target_reached) == Root::Conflict
            {
                return self.on_root_conflict();
            }

            // ---- FSM with hysteresis ----
            let obs = Observation {
                improved,
                best_unsat: self.best_unsat,
                n_clauses: self.n_orig,
                time_frac: (Instant::now() - self.t0).as_secs_f32() / (self.cfg.timeout_ms as f32 / 1000.0).max(1e-3),
                relax_exhausted: self.relax_exhausted(),
            };
            if let Some(t) = self.ctrl.observe(&obs) {
                self.emit_mode(t);
                self.apply_mode();
                let rr = if t.1 == Mode::Conservative { self.unmask_all() } else { Root::Ok };
                // in-processing on every tier change (Module 6)
                if rr == Root::Conflict || self.inprocess() == Root::Conflict {
                    return self.on_root_conflict();
                }
            }
        }
        self.emit(EventKind::Timeout);
        Status::Unknown
    }
}

#[doc(hidden)]
impl SolverWorkspace {
    /// Diagnostic: run pure SLS (strict, all clauses) for `ms`. Returns (best unsat, flips).
    pub fn diag_sls(&mut self, ms: u64) -> (u32, u64) {
        let end = Instant::now() + Duration::from_millis(ms);
        let mut t = Ticker::new(end, 128);
        let o = self.sls_run(SlsStart::Random, 0, u64::MAX, PARAMS[0].sls_noise, &mut t);
        (o.best, o.flips)
    }
}
