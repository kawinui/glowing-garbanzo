//! Module 2: fast stochastic local search over flat, packed arrays.
//!
//! Per clause one 16-byte `SlsClause` record {true_count, true_xor, weight,
//! unsat-list position}: a flip touches one cache line per affected clause.
//! `true_xor` is the XOR of the variables of the clause's true literals, so
//! when `true_count == 1` it *is* the critical variable and break counts are
//! maintained without re-scanning the clause.
//! Per variable: weighted `brk` (sum of weights of clauses where it is the sole
//! true literal) and — for the `Steepest` rule — weighted `make`.
//! The unsat set is an index list with O(1) swap-removal, mirrored in a
//! bit-vector that is cross-checked with hardware popcount.
//!
//! Masked clauses (progressive relaxation) carry weight 0 and are kept out of
//! the unsat set. Permanent penalty weights learnt by the controller are the
//! starting weights of every run.

use crate::arena::SolverWorkspace;
use crate::types::*;
use crate::util::*;

#[repr(C, align(16))]
#[derive(Copy, Clone, Default, Debug)]
pub struct SlsClause {
    pub tc: u32,
    pub xor: u32,
    pub w: u32,
    pub pos: u32,
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum SlsStart {
    /// Continue from the current SLS state (falls back to `Best` if stale).
    Resume,
    /// Anytime-best assignment with light random perturbation.
    Best,
    /// Current saved phases.
    Phase,
    /// Uniformly random.
    Random,
}

#[derive(Copy, Clone, Debug)]
pub struct SlsOutcome {
    /// Min active-unsat count reached in this run (assignment in `sls_best`).
    pub best: u32,
    pub flips: u64,
    pub reached_target: bool,
}

const DYN_WEIGHT_CAP: u32 = 1 << 22;
pub(crate) const PROB_CB: f32 = 2.38;

/// probSAT polynomial table: (1 + b)^-cb for b in 0..256 (built at load time).
pub(crate) fn prob_table() -> [f32; 256] {
    let mut t = [0f32; 256];
    for (b, x) in t.iter_mut().enumerate() {
        *x = (1.0 + b as f32).powf(-PROB_CB);
    }
    t
}

impl SolverWorkspace {
    #[inline(always)]
    fn sls_true(&self, l: Lit) -> bool {
        self.sls_val.get(l.var() as usize) != l.is_neg()
    }

    #[inline(always)]
    fn unsat_push(&mut self, c: u32) {
        at_mut(&mut self.sls_c, c as usize).pos = self.unsat_len;
        *at_mut(&mut self.unsat_list, self.unsat_len as usize) = c;
        self.unsat_len += 1;
        self.unsat_bits.set(c as usize);
    }

    #[inline(always)]
    fn unsat_remove(&mut self, c: u32) {
        let p = at(&self.sls_c, c as usize).pos;
        self.unsat_len -= 1;
        let last = at(&self.unsat_list, self.unsat_len as usize);
        *at_mut(&mut self.unsat_list, p as usize) = last;
        at_mut(&mut self.sls_c, last as usize).pos = p;
        at_mut(&mut self.sls_c, c as usize).pos = NIL;
        self.unsat_bits.clear(c as usize);
    }

    #[inline(always)]
    fn add_make(&mut self, c: usize, w: u64, add: bool) {
        let (s, e) = self.orig_range(c);
        for k in s..e {
            let v = at(&self.orig_lits, k).var() as usize;
            let m = at_mut(&mut self.make, v);
            if add {
                *m += w;
            } else {
                *m -= w;
            }
        }
    }

    /// Rebuild all SLS bookkeeping from `sls_val` (O(total literals)).
    fn sls_init_state(&mut self, track_make: bool) {
        if track_make {
            self.make.fill(0);
        }
        self.brk.fill(0);
        self.unsat_len = 0;
        self.unsat_bits.clear_all();
        for c in 0..self.n_orig as usize {
            let active = self.hot.all_active || self.active.get(c);
            let w = if active { at(&self.clause_weight, c) } else { 0 };
            let (s, e) = self.orig_range(c);
            let mut tc = 0u32;
            let mut x = 0u32;
            for k in s..e {
                let l = at(&self.orig_lits, k);
                let t = self.sls_true(l) as u32; // branch-free accumulate
                tc += t;
                x ^= l.var() & t.wrapping_neg();
            }
            *at_mut(&mut self.sls_c, c) = SlsClause { tc, xor: x, w, pos: NIL };
            if tc == 0 {
                if w > 0 {
                    self.unsat_push(c as u32);
                    if track_make {
                        self.add_make(c, w as u64, true);
                    }
                }
            } else if tc == 1 {
                *at_mut(&mut self.brk, x as usize) += w as u64;
            }
        }
        self.sls_tracks_make = track_make;
    }

    /// Flip `v`, updating counts incrementally.
    #[inline]
    fn sls_flip(&mut self, v: u32, track_make: bool) {
        let was_true = self.sls_val.get(v as usize);
        self.sls_val.toggle(v as usize);
        let now_true = Lit::new(v, was_true); // literal of v that just became true
        let (s, e) = self.occ_range(now_true);
        for i in s..e {
            let c = at(&self.occ, i) as usize;
            let sc = at(&self.sls_c, c);
            let w = sc.w as u64;
            if sc.tc == 0 {
                if w > 0 {
                    self.unsat_remove(c as u32);
                    if track_make {
                        self.add_make(c, w, false);
                    }
                }
                *at_mut(&mut self.brk, v as usize) += w;
            } else if sc.tc == 1 {
                *at_mut(&mut self.brk, sc.xor as usize) -= w;
            }
            let r = at_mut(&mut self.sls_c, c);
            r.tc += 1;
            r.xor ^= v;
        }
        let (s, e) = self.occ_range(!now_true);
        for i in s..e {
            let c = at(&self.occ, i) as usize;
            let r = at_mut(&mut self.sls_c, c);
            r.tc -= 1;
            r.xor ^= v;
            let sc = *r;
            let w = sc.w as u64;
            if sc.tc == 0 {
                if w > 0 {
                    self.unsat_push(c as u32);
                    if track_make {
                        self.add_make(c, w, true);
                    }
                }
                *at_mut(&mut self.brk, v as usize) -= w;
            } else if sc.tc == 1 {
                *at_mut(&mut self.brk, sc.xor as usize) += w;
            }
        }
    }

    /// Increase the dynamic weight of every currently unsat clause by one.
    fn sls_bump_unsat_weights(&mut self) {
        for i in 0..self.unsat_len as usize {
            let c = at(&self.unsat_list, i) as usize;
            let r = at_mut(&mut self.sls_c, c);
            if r.w < DYN_WEIGHT_CAP {
                r.w += 1;
                self.add_make(c, 1, true);
            }
        }
    }

    /// One SLS run. Stops at `target` active-unsat clauses, `max_flips`, or deadline.
    pub(crate) fn sls_run(&mut self, start: SlsStart, target: u32, max_flips: u64, base_noise: f32, ticker: &mut Ticker) -> SlsOutcome {
        let n = self.n_vars as usize;
        let track_make = self.cfg.sls_rule == SlsRule::Steepest;
        let root = self.root_len();
        let resumable = self.sls_ready
            && self.sls_root_len == root
            && self.sls_masked == self.num_masked
            && self.sls_tracks_make == track_make;
        let start = match start {
            SlsStart::Resume if resumable => SlsStart::Resume,
            SlsStart::Resume => {
                if self.best_unsat == u32::MAX {
                    SlsStart::Phase
                } else {
                    SlsStart::Best
                }
            }
            s => s,
        };
        if start != SlsStart::Resume {
            self.frozen.clear_all();
            match start {
                SlsStart::Best => {
                    self.sls_val.copy_from(&self.best);
                    let k = (n / 500).clamp(1, 64);
                    for _ in 0..k {
                        if n > 0 {
                            let v = self.rng.below(n as u32) as usize;
                            self.sls_val.toggle(v);
                        }
                    }
                }
                SlsStart::Phase => self.sls_val.copy_from(&self.phase),
                _ => self.sls_val.fill_random(&mut self.rng),
            }
            // root-fixed variables are frozen at their value
            for i in 0..root as usize {
                let l = at(&self.trail, i);
                self.frozen.set(l.var() as usize);
                self.sls_val.assign(l.var() as usize, !l.is_neg());
            }
            self.sls_init_state(track_make);
            self.sls_ready = true;
            self.sls_root_len = root;
            self.sls_masked = self.num_masked;
        }

        let mut best = self.unsat_len;
        self.sls_best.copy_from(&self.sls_val);
        let mut trail_len = 0usize;
        let mut flips = 0u64;
        let mut noise = base_noise;
        let mut since_improve = 0u64;
        let stall_window = (self.n_orig as u64 / 8).max(64);
        let hybrid = self.hot.hybrid_scoring;
        let mut stuck = 0u32;
        let mut cand_v = [0u32; 32];
        let mut cand_p = [0f32; 32];
        while self.unsat_len > target && flips < max_flips {
            if ticker.tick() {
                break;
            }
            let c = at(&self.unsat_list, self.rng.below(self.unsat_len) as usize) as usize;
            let (s, e) = self.orig_range(c);
            let v = if !track_make {
                // ---- probSAT rule: P(v) ∝ (1 + break)^-cb ----
                let mut m = 0usize;
                let mut tot = 0f32;
                for k in s..e {
                    let v = at(&self.orig_lits, k).var();
                    if self.frozen.get(v as usize) || m == 32 {
                        continue;
                    }
                    let b = at(&self.brk, v as usize);
                    let p = if b < 256 { self.prob_tab[b as usize] } else { (1.0 + b as f32).powf(-PROB_CB) };
                    tot += p;
                    cand_v[m] = v;
                    cand_p[m] = tot;
                    m += 1;
                }
                if m == 0 {
                    NIL
                } else {
                    let r = self.rng.next_f32() * tot;
                    let mut i = 0usize;
                    while i + 1 < m && cand_p[i] < r {
                        i += 1;
                    }
                    cand_v[i]
                }
            } else {
                // ---- steepest weighted make − break with adaptive noise ----
                let mut best_v = NIL;
                let mut best_sc = i64::MIN;
                let mut free_v = NIL;
                let mut free_n = 0u32;
                let mut walk_v = NIL;
                let mut nflip = 0u32;
                for k in s..e {
                    let v = at(&self.orig_lits, k).var();
                    if self.frozen.get(v as usize) {
                        continue;
                    }
                    nflip += 1;
                    if self.rng.below(nflip) == 0 {
                        walk_v = v;
                    }
                    let b = at(&self.brk, v as usize);
                    if b == 0 {
                        free_n += 1;
                        if self.rng.below(free_n) == 0 {
                            free_v = v;
                        }
                    }
                    let sc = at(&self.make, v as usize) as i64 - b as i64;
                    if sc > best_sc || (sc == best_sc && self.rng.next_u32() & 1 == 0) {
                        best_sc = sc;
                        best_v = v;
                    }
                }
                if nflip == 0 {
                    NIL
                } else if free_v != NIL {
                    free_v
                } else if self.rng.chance(noise) {
                    walk_v
                } else {
                    // local minimum: PAWS-style weight bump, rate-limited so the
                    // expected cost per flip stays O(1) even with many unsat clauses
                    if best_sc <= 0 && self.rng.chance((16.0 / self.unsat_len as f32).min(0.15)) {
                        self.sls_bump_unsat_weights();
                    }
                    best_v
                }
            };
            if v == NIL {
                // clause falsified by root facts alone; CDCL will refute it
                stuck += 1;
                if stuck > 64 {
                    break;
                }
                continue;
            }
            let before = self.unsat_len;
            self.sls_flip(v, track_make);
            flips += 1;
            if hybrid && self.unsat_len < before {
                self.bump_raw(v, 1);
            }
            // lazy best tracking: remember flips since the last snapshot
            if trail_len < n {
                *at_mut(&mut self.flip_trail, trail_len) = v;
            }
            trail_len += 1;
            if self.unsat_len < best {
                best = self.unsat_len;
                if trail_len <= n {
                    for i in 0..trail_len {
                        let x = at(&self.flip_trail, i) as usize;
                        let b = self.sls_val.get(x);
                        self.sls_best.assign(x, b);
                    }
                } else {
                    self.sls_best.copy_from(&self.sls_val); // fast slice copy
                }
                trail_len = 0;
                since_improve = 0;
                noise -= noise * 0.2;
            } else {
                since_improve += 1;
                if since_improve > stall_window {
                    noise += (0.6 - noise) * 0.2;
                    since_improve = 0;
                }
            }
        }
        debug_assert_eq!(self.unsat_bits.count_ones(), self.unsat_len);
        self.stats.sls_flips += flips;
        if hybrid {
            self.order_rebuild();
        }
        SlsOutcome { best, flips, reached_target: best <= target }
    }
}
