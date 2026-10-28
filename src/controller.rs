//! Module 7: closed-loop adaptive controller.
//!
//! * `Controller` — deterministic 3-state FSM (Aggressive / Balanced /
//!   Conservative) with hysteresis: a minimum dwell time per mode plus
//!   asymmetric streak thresholds (2 improving epochs to move "up",
//!   3 stalled epochs to move "down"), so the mode cannot oscillate.
//! * `QTable` — contextual multi-armed bandit over the operator space,
//!   stored in a fixed `[f32; NUM_STATES * NUM_ACTIONS]` table and updated
//!   in place with an exponential recency-weighted average
//!   `Q(s,a) <- Q(s,a) + alpha * (R - Q(s,a))`.

use crate::types::*;
use crate::util::Rng;

/// Per-mode operating parameters.
#[derive(Copy, Clone, Debug)]
pub struct ModeParams {
    /// Micro-timeout per epoch (Conservative grows geometrically from this base).
    pub micro_ms: u64,
    /// Relaxation ceiling `k` as ppm of clauses.
    pub k_ppm: u32,
    /// Conflicts between activity-increment doublings (== halving all scores).
    /// Small = high-frequency scoring updates.
    pub decay_interval: u32,
    /// Base SLS random-walk noise.
    pub sls_noise: f32,
}

pub const PARAMS: [ModeParams; 3] = [
    ModeParams { micro_ms: 15, k_ppm: 20_000, decay_interval: 8, sls_noise: 0.20 },
    ModeParams { micro_ms: 75, k_ppm: 5_000, decay_interval: 16, sls_noise: 0.12 },
    ModeParams { micro_ms: 250, k_ppm: 0, decay_interval: 32, sls_noise: 0.08 },
];

const MIN_DWELL: u32 = 2;
const UP_STREAK: u32 = 2;
const DOWN_STREAK: u32 = 3;
const ESCAPE_STREAK: u32 = 8;
pub const TIME_PRESSURE: f32 = 0.6;

/// What the solver reports to the controller after each epoch.
#[derive(Copy, Clone, Debug)]
pub struct Observation {
    pub improved: bool,
    pub best_unsat: u32,
    pub n_clauses: u32,
    pub time_frac: f32,
    pub relax_exhausted: bool,
}

#[repr(C, align(64))]
#[derive(Clone, Debug)]
pub struct Controller {
    pub mode: Mode,
    pub dwell: u32,
    pub improve_streak: u32,
    pub stall_streak: u32,
    pub conservative_epochs: u32,
    pub transitions: u32,
    /// Time accounting in Conservative mode (completeness guard).
    pub cons_cdcl_us: u64,
    pub cons_other_us: u64,
}

impl Default for Controller {
    fn default() -> Self {
        Self::new()
    }
}

impl Controller {
    pub fn new() -> Self {
        Controller {
            mode: Mode::Aggressive,
            dwell: 0,
            improve_streak: 0,
            stall_streak: 0,
            conservative_epochs: 0,
            transitions: 0,
            cons_cdcl_us: 0,
            cons_other_us: 0,
        }
    }

    #[inline]
    pub fn params(&self) -> &'static ModeParams {
        &PARAMS[self.mode.idx()]
    }

    /// Bandit context: mode × {improving, stalling}.
    #[inline]
    pub fn context(&self) -> usize {
        self.mode.idx() * 2 + (self.stall_streak > 0) as usize
    }

    /// Micro-timeout for the next epoch.
    pub fn micro_ms(&self, remaining_ms: u64) -> u64 {
        let base = self.params().micro_ms;
        let ms = match self.mode {
            Mode::Conservative => base << (self.conservative_epochs / 4).min(3),
            _ => base,
        };
        ms.min(remaining_ms).max(1)
    }

    /// Completeness guard: in Conservative mode CDCL must own >= 50% of time.
    pub fn must_force_cdcl(&self) -> bool {
        self.mode == Mode::Conservative && {
            let tot = self.cons_cdcl_us + self.cons_other_us;
            tot > 0 && (self.cons_cdcl_us as f64) < 0.5 * tot as f64
        }
    }

    pub fn account(&mut self, cdcl: bool, us: u64) {
        if self.mode == Mode::Conservative {
            if cdcl {
                self.cons_cdcl_us += us;
            } else {
                self.cons_other_us += us;
            }
            self.conservative_epochs += 1;
        }
    }

    /// Unconditional transition (proof escalation / model verification).
    pub fn force(&mut self, to: Mode, why: Why) -> Option<(Mode, Mode, Why)> {
        if self.mode == to {
            return None;
        }
        Some(self.go(to, why))
    }

    fn go(&mut self, to: Mode, why: Why) -> (Mode, Mode, Why) {
        let from = self.mode;
        self.mode = to;
        self.dwell = 0;
        self.improve_streak = 0;
        self.stall_streak = 0;
        self.transitions += 1;
        (from, to, why)
    }

    /// Feed one epoch's outcome; returns a transition if the FSM fires.
    pub fn observe(&mut self, o: &Observation) -> Option<(Mode, Mode, Why)> {
        self.dwell += 1;
        if o.improved {
            self.improve_streak += 1;
            self.stall_streak = 0;
        } else {
            self.stall_streak += 1;
            self.improve_streak = 0;
        }
        let near = o.best_unsat <= (o.n_clauses / 2000).max(2);
        if self.dwell < MIN_DWELL {
            return None;
        }
        match self.mode {
            Mode::Aggressive => {
                if o.time_frac >= TIME_PRESSURE {
                    Some(self.go(Mode::Conservative, Why::TimePressure))
                } else if near {
                    Some(self.go(Mode::Conservative, Why::NearSolution))
                } else if self.improve_streak >= UP_STREAK {
                    Some(self.go(Mode::Balanced, Why::SteadyProgress))
                } else if o.relax_exhausted && self.stall_streak > DOWN_STREAK {
                    Some(self.go(Mode::Balanced, Why::RelaxExhausted))
                } else {
                    None
                }
            }
            Mode::Balanced => {
                if o.time_frac >= TIME_PRESSURE {
                    Some(self.go(Mode::Conservative, Why::TimePressure))
                } else if near {
                    Some(self.go(Mode::Conservative, Why::NearSolution))
                } else if o.relax_exhausted && self.stall_streak >= DOWN_STREAK {
                    Some(self.go(Mode::Conservative, Why::RelaxExhausted))
                } else if self.stall_streak >= DOWN_STREAK {
                    Some(self.go(Mode::Aggressive, Why::Stagnation))
                } else {
                    None
                }
            }
            Mode::Conservative => {
                if self.stall_streak >= ESCAPE_STREAK
                    && self.dwell >= ESCAPE_STREAK
                    && o.time_frac < 0.4
                    && !near
                {
                    Some(self.go(Mode::Balanced, Why::EscapeStall))
                } else {
                    None
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Q-table bandit
// ---------------------------------------------------------------------------

pub const NUM_STATES: usize = 6;

pub const W_UNSAT: f32 = 1.0;
pub const W_ROOT: f32 = 0.5;
pub const W_COST: f32 = 0.05;

/// Bounded reward `R = w1·Δunsat + w2·Δroot − w3·cost`, clamped to [-1, 1].
/// `d_unsat` and `d_root` are relative improvements in [0,1]; `cost` is work
/// spent relative to the running average (≈1 for a typical epoch).
#[inline]
pub fn reward(d_unsat: f32, d_root: f32, cost: f32) -> f32 {
    (W_UNSAT * d_unsat + W_ROOT * d_root - W_COST * cost).clamp(-1.0, 1.0)
}

#[repr(C, align(64))]
#[derive(Clone, Debug)]
pub struct QTable {
    pub q: [f32; NUM_STATES * NUM_ACTIONS],
    pub n: [u32; NUM_STATES * NUM_ACTIONS],
    pub alpha: f32,
    pub eps: f32,
    rr: u32,
}

impl Default for QTable {
    fn default() -> Self {
        Self::new()
    }
}

impl QTable {
    pub fn new() -> Self {
        QTable {
            q: [0.0; NUM_STATES * NUM_ACTIONS],
            n: [0; NUM_STATES * NUM_ACTIONS],
            alpha: 0.25,
            eps: 0.30,
            rr: 0,
        }
    }

    /// Choose an action among `allowed` (bitmask over `Action::idx`).
    /// Untried arms are tried first (the "trial" phase), then ε-greedy.
    pub fn select(&mut self, s: usize, allowed: u32, rng: &mut Rng, learning: bool) -> Action {
        debug_assert!(allowed != 0);
        if !learning {
            // fixed round-robin policy (ablation baseline)
            loop {
                let a = (self.rr as usize) % NUM_ACTIONS;
                self.rr = self.rr.wrapping_add(1);
                if allowed & (1 << a) != 0 {
                    return Action::ALL[a];
                }
            }
        }
        let base = s * NUM_ACTIONS;
        // trial phase: any allowed untried arm in this context
        let mut untried = 0u32;
        for a in 0..NUM_ACTIONS {
            if allowed & (1 << a) != 0 && self.n[base + a] == 0 {
                untried |= 1 << a;
            }
        }
        let pick_from = |mask: u32, rng: &mut Rng| -> usize {
            let k = rng.below(mask.count_ones());
            let mut m = mask;
            for _ in 0..k {
                m &= m - 1;
            }
            m.trailing_zeros() as usize
        };
        if untried != 0 {
            return Action::ALL[pick_from(untried, rng)];
        }
        if rng.chance(self.eps) {
            return Action::ALL[pick_from(allowed, rng)];
        }
        let mut best = usize::MAX;
        let mut bq = f32::NEG_INFINITY;
        for a in 0..NUM_ACTIONS {
            if allowed & (1 << a) == 0 {
                continue;
            }
            let q = self.q[base + a];
            if q > bq || (q == bq && rng.next_u32() & 1 == 0) {
                bq = q;
                best = a;
            }
        }
        Action::ALL[best]
    }

    /// Greedy choice restricted to a mask (used by the completeness guard).
    pub fn best_in(&self, s: usize, mask: u32) -> Action {
        let base = s * NUM_ACTIONS;
        let mut best = mask.trailing_zeros() as usize;
        for a in 0..NUM_ACTIONS {
            if mask & (1 << a) != 0 && self.q[base + a] > self.q[base + best] {
                best = a;
            }
        }
        Action::ALL[best]
    }

    /// ERWA update in place.
    pub fn update(&mut self, s: usize, a: Action, r: f32) {
        let i = s * NUM_ACTIONS + a.idx();
        let q = &mut self.q[i];
        *q += self.alpha * (r - *q);
        self.n[i] = self.n[i].saturating_add(1);
        self.eps = (self.eps * 0.985).max(0.05);
    }
}
