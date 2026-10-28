//! Bounded CDCL engine (the only component that can *prove* UNSAT).
//!
//! * 1-UIP conflict analysis, iterative, with local (non-recursive) clause
//!   minimisation and LBD computation via level stamps.
//! * Learnt clauses go into a fixed-capacity arena. When it fills, the DB is
//!   reduced in place at level 0: an LBD histogram picks the deletion
//!   threshold (no sorting), survivors are compacted with `copy_within`, and
//!   watches are rebuilt. Glue clauses (LBD <= 2) are always kept.
//! * Luby restarts; bursts are bounded by conflicts and a micro-deadline.

use crate::arena::SolverWorkspace;
use crate::propagate::Root;
use crate::types::*;
use crate::util::*;

const RESTART_UNIT: u32 = 64;
const WEIGHT_CAP: u32 = 1 << 20;

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum Burst {
    /// Full assignment satisfying every *active* clause (model in `self.model`).
    Sat,
    /// Conflict at decision level 0.
    RootConflict,
    /// Budget / deadline exhausted.
    Budget,
}

/// Luby sequence (iterative, MiniSat formulation).
pub fn luby(mut x: u32) -> u32 {
    let mut size = 1u32;
    let mut seq = 0u32;
    while size < x + 1 {
        seq += 1;
        size = 2 * size + 1;
    }
    while size - 1 != x {
        size = (size - 1) >> 1;
        seq -= 1;
        x %= size;
    }
    1u32 << seq.min(20)
}

impl SolverWorkspace {
    /// 1-UIP analysis. Writes the learnt clause to `learnt_buf[0..len]`
    /// (asserting literal at 0, highest-level literal at 1).
    /// Returns (backtrack level, len, lbd).
    pub(crate) fn analyze(&mut self, confl: u32) -> (u32, usize, u32) {
        let dl = self.hot.dlevel;
        let mut out = 1usize;
        let mut pathc = 0u32;
        let mut p = Lit::UNDEF;
        let mut idx = self.hot.trail_len as usize;
        let mut c = confl;
        loop {
            debug_assert!(c != NIL);
            let h = at(&self.hdr, c as usize);
            let s = h.start as usize;
            let e = s + h.len as usize;
            for k in s..e {
                let q = at(&self.lits, k);
                let v = q.var();
                if v == p.var() {
                    continue;
                }
                if at(&self.seen, v as usize) == 0 && at(&self.level, v as usize) > 0 {
                    *at_mut(&mut self.seen, v as usize) = 1;
                    self.bump_var(v);
                    if at(&self.level, v as usize) >= dl {
                        pathc += 1;
                    } else {
                        *at_mut(&mut self.learnt_buf, out) = q;
                        out += 1;
                    }
                }
            }
            loop {
                idx -= 1;
                if at(&self.seen, at(&self.trail, idx).var() as usize) != 0 {
                    break;
                }
            }
            p = at(&self.trail, idx);
            *at_mut(&mut self.seen, p.var() as usize) = 0;
            pathc -= 1;
            if pathc == 0 {
                break;
            }
            c = at(&self.reason, p.var() as usize);
        }
        *at_mut(&mut self.learnt_buf, 0) = !p;

        // local minimisation: drop q if its reason is subsumed by the clause
        let total = out;
        for i in 1..total {
            *at_mut(&mut self.clear_buf, i) = at(&self.learnt_buf, i);
        }
        let mut j = 1usize;
        for i in 1..total {
            let q = at(&self.learnt_buf, i);
            let r = at(&self.reason, q.var() as usize);
            let keep = if r == NIL {
                true
            } else {
                let h = at(&self.hdr, r as usize);
                let s = h.start as usize;
                let mut keep = false;
                for k in s..s + h.len as usize {
                    let x = at(&self.lits, k).var() as usize;
                    if x != q.var() as usize && at(&self.seen, x) == 0 && at(&self.level, x) > 0 {
                        keep = true;
                        break;
                    }
                }
                keep
            };
            if keep {
                *at_mut(&mut self.learnt_buf, j) = q;
                j += 1;
            }
        }
        out = j;
        for i in 1..total {
            *at_mut(&mut self.seen, at(&self.clear_buf, i).var() as usize) = 0;
        }

        // backtrack level: move max-level literal to position 1
        let bt = if out == 1 {
            0
        } else {
            let mut mi = 1;
            for i in 2..out {
                if at(&self.level, at(&self.learnt_buf, i).var() as usize)
                    > at(&self.level, at(&self.learnt_buf, mi).var() as usize)
                {
                    mi = i;
                }
            }
            self.learnt_buf.swap(1, mi);
            at(&self.level, at(&self.learnt_buf, 1).var() as usize)
        };

        // LBD via level stamps
        if self.hot.level_gen == u32::MAX {
            self.level_stamp.fill(0);
            self.hot.level_gen = 0;
        }
        self.hot.level_gen += 1;
        let g = self.hot.level_gen;
        let mut lbd = 0u32;
        for i in 0..out {
            let lv = at(&self.level, at(&self.learnt_buf, i).var() as usize) as usize;
            if at(&self.level_stamp, lv) != g {
                *at_mut(&mut self.level_stamp, lv) = g;
                lbd += 1;
            }
        }
        (bt, out, lbd)
    }

    /// Store `learnt_buf[0..len]` after backtracking to its assertion level.
    /// Returns false when the fixed arena is full.
    fn add_learnt(&mut self, len: usize, lbd: u32) -> bool {
        if self.hot.num_learnt >= self.learnt_clause_cap
            || self.hot.learnt_top as usize + len > self.lits.len()
        {
            return false;
        }
        let c = self.n_orig + self.hot.num_learnt;
        let start = self.hot.learnt_top as usize;
        self.lits[start..start + len].copy_from_slice(&self.learnt_buf[..len]);
        *at_mut(&mut self.hdr, c as usize) = ClauseHeader {
            start: start as u32,
            len: len as u32,
            lbd: lbd.min(u16::MAX as u32) as u16,
            flags: F_LEARNT,
            birth: self.stats.conflicts as u32,
        };
        self.hot.num_learnt += 1;
        self.hot.learnt_top += len as u32;
        self.attach(c);
        self.enqueue(at(&self.learnt_buf, 0), c);
        true
    }

    /// Add `learnt_buf[0..len]` at level 0 (after an emergency reduction).
    /// Reorders literals so the two watches are non-false.
    fn add_learnt_root(&mut self, len: usize, lbd: u32) -> Root {
        debug_assert_eq!(self.hot.dlevel, 0);
        let mut j = 0usize;
        for i in 0..len {
            let l = at(&self.learnt_buf, i);
            match self.value(l) {
                V_TRUE => return Root::Ok, // satisfied at root, nothing to keep
                V_UNDEF => {
                    *at_mut(&mut self.learnt_buf, j) = l;
                    j += 1;
                }
                _ => {}
            }
        }
        match j {
            0 => Root::Conflict,
            1 => {
                self.enqueue(at(&self.learnt_buf, 0), NIL);
                self.stats.learnt_units += 1;
                if self.propagate() != NIL {
                    Root::Conflict
                } else {
                    Root::Ok
                }
            }
            _ => {
                if self.hot.num_learnt < self.learnt_clause_cap
                    && self.hot.learnt_top as usize + j <= self.lits.len()
                {
                    let c = self.n_orig + self.hot.num_learnt;
                    let start = self.hot.learnt_top as usize;
                    self.lits[start..start + j].copy_from_slice(&self.learnt_buf[..j]);
                    *at_mut(&mut self.hdr, c as usize) = ClauseHeader {
                        start: start as u32,
                        len: j as u32,
                        lbd: lbd.min(u16::MAX as u32) as u16,
                        flags: F_LEARNT,
                        birth: self.stats.conflicts as u32,
                    };
                    self.hot.num_learnt += 1;
                    self.hot.learnt_top += j as u32;
                    self.attach(c);
                }
                // else: arena too small even after reduction; dropping a learnt
                // clause is always sound (it is implied).
                Root::Ok
            }
        }
    }

    /// In-place clause-DB reduction at level 0.
    pub(crate) fn reduce_db(&mut self) -> Root {
        debug_assert_eq!(self.hot.dlevel, 0);
        let base = self.n_orig as usize;
        let nl = self.hot.num_learnt as usize;
        // LBD histogram (bucket 32 = ">= 32") over deletable clauses
        let mut hist = [0u32; 33];
        for c in base..base + nl {
            let h = at(&self.hdr, c);
            if h.flags & F_DELETED == 0 && h.lbd > 2 {
                hist[(h.lbd as usize).min(32)] += 1;
            }
        }
        let cand: u32 = hist.iter().sum();
        let target = cand / 2;
        let mut thr = 33usize;
        let mut quota = 0u32;
        let mut acc = 0u32;
        if target > 0 {
            let mut b = 32usize;
            loop {
                if acc + hist[b] >= target {
                    thr = b;
                    quota = target - acc;
                    break;
                }
                acc += hist[b];
                b -= 1;
            }
        }
        let mut deleted = 0u32;
        for c in base..base + nl {
            let h = at_mut(&mut self.hdr, c);
            if h.flags & F_DELETED != 0 || h.lbd <= 2 {
                continue;
            }
            let b = (h.lbd as usize).min(32);
            if b > thr || (b == thr && quota > 0) {
                if b == thr {
                    quota -= 1;
                }
                h.flags |= F_DELETED;
                deleted += 1;
            }
        }
        // root reasons may point at learnt clauses: clear before compaction
        for i in 0..self.hot.trail_len as usize {
            let v = at(&self.trail, i).var() as usize;
            *at_mut(&mut self.reason, v) = NIL;
        }
        // compact the learnt arena (stable order => age order preserved)
        let mut w = 0usize;
        let mut top = self.learnt_base as usize;
        for i in 0..nl {
            let h = at(&self.hdr, base + i);
            if h.flags & F_DELETED != 0 {
                continue;
            }
            let s = h.start as usize;
            let len = h.len as usize;
            self.lits.copy_within(s..s + len, top);
            *at_mut(&mut self.hdr, base + w) = ClauseHeader { start: top as u32, ..h };
            top += len;
            w += 1;
        }
        self.hot.num_learnt = w as u32;
        self.hot.learnt_top = top as u32;
        self.stats.reductions += 1;
        self.hot.reduce_target = (self.hot.reduce_target + 300).min(self.learnt_clause_cap * 3 / 4).max(16);
        self.emit(EventKind::Reduce { kept: w as u32, deleted });
        self.root_simplify_and_rebuild()
    }

    /// One bounded CDCL run from level 0.
    pub(crate) fn cdcl_burst(&mut self, max_conflicts: u64, ticker: &mut Ticker) -> Burst {
        self.backtrack(0);
        #[cfg(debug_assertions)]
        self.check_watches("burst-start");
        let start = self.stats.conflicts;
        let mut restart_limit = luby(self.hot.luby_idx) * RESTART_UNIT;
        loop {
            let confl = self.propagate();
            if confl != NIL {
                self.stats.conflicts += 1;
                if self.hot.dlevel == 0 {
                    return Burst::RootConflict;
                }
                // permanent clause-penalty learning: conflict sources get heavier
                if confl < self.n_orig {
                    let w = at_mut(&mut self.clause_weight, confl as usize);
                    *w = (*w + 1).min(WEIGHT_CAP);
                }
                let (bt, len, lbd) = self.analyze(confl);
                self.backtrack(bt);
                if len == 1 {
                    self.enqueue(at(&self.learnt_buf, 0), NIL);
                    self.stats.learnt_units += 1;
                } else if !self.add_learnt(len, lbd) {
                    // arena full: emergency in-place reduction at root
                    self.backtrack(0);
                    if self.reduce_db() == Root::Conflict || self.add_learnt_root(len, lbd) == Root::Conflict {
                        return Burst::RootConflict;
                    }
                }
                self.decay_tick();
                self.hot.since_restart += 1;
                if self.hot.since_restart >= restart_limit {
                    self.hot.since_restart = 0;
                    self.hot.luby_idx += 1;
                    restart_limit = luby(self.hot.luby_idx) * RESTART_UNIT;
                    self.stats.restarts += 1;
                    self.backtrack(0);
                    if self.hot.num_learnt >= self.hot.reduce_target && self.reduce_db() == Root::Conflict {
                        return Burst::RootConflict;
                    }
                }
                if self.stats.conflicts - start >= max_conflicts || ticker.tick() {
                    self.backtrack(0);
                    return Burst::Budget;
                }
            } else {
                if ticker.tick() {
                    self.backtrack(0);
                    return Burst::Budget;
                }
                let v = self.pick_branch();
                if v == NIL {
                    // complete assignment, every active clause satisfied
                    for i in 0..self.hot.trail_len as usize {
                        let l = at(&self.trail, i);
                        self.model.assign(l.var() as usize, !l.is_neg());
                    }
                    self.backtrack(0);
                    return Burst::Sat;
                }
                self.stats.decisions += 1;
                self.new_level();
                let lit = Lit::new(v, !self.phase.get(v as usize));
                self.enqueue(lit, NIL);
            }
        }
    }
}
