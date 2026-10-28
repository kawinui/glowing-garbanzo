//! Module 3: lightweight lookahead / failed-literal probing at level 0.
//!
//! Top-K candidates are selected with a fixed-size insertion buffer (no sort,
//! no heap) by `(activity >> penalty, occ(+v)·occ(−v))`. For each candidate:
//! probe `v`, then `¬v`, each with bounded propagation.
//! * a probe that conflicts ⇒ the opposite literal is a root fact;
//! * literals implied by *both* polarities ⇒ root facts;
//! * a candidate that yields nothing gets a probe penalty (dead end), which
//!   lowers its priority for future probing rounds;
//! * variables of a failing probe's conflict clause get activity bumps.
//!
//! Every derived fact is an implication of the active clauses (+ learnt
//! clauses), hence of the full formula: probing is sound in every tier.

use crate::arena::SolverWorkspace;
use crate::propagate::Root;
use crate::types::*;
use crate::util::*;

pub const PROBE_K: usize = 32;

#[derive(Copy, Clone, Debug)]
pub struct ProbeOutcome {
    pub fixed: u32,
    pub failed: u32,
    pub root: Root,
}

impl SolverWorkspace {
    fn select_probe_candidates(&mut self, out: &mut [u32; PROBE_K]) -> usize {
        let mut key = [0u64; PROBE_K];
        let mut nc = 0usize;
        for v in 0..self.n_vars {
            if self.is_assigned(v) {
                continue;
            }
            let pen = at(&self.probe_penalty, v as usize) as u32;
            let (ps, pe) = self.occ_range(Lit::new(v, false));
            let (ns, ne) = self.occ_range(Lit::new(v, true));
            let prod = ((pe - ps) as u64 * (ne - ns) as u64).min((1 << 20) - 1);
            if prod == 0 {
                continue; // pure or absent: probing cannot fail both ways
            }
            let k = (((at(&self.score, v as usize) >> pen) as u64) << 20 | prod) >> pen;
            if nc < PROBE_K {
                let mut i = nc;
                while i > 0 && key[i - 1] < k {
                    key[i] = key[i - 1];
                    out[i] = out[i - 1];
                    i -= 1;
                }
                key[i] = k;
                out[i] = v;
                nc += 1;
            } else if k > key[PROBE_K - 1] {
                let mut i = PROBE_K - 1;
                while i > 0 && key[i - 1] < k {
                    key[i] = key[i - 1];
                    out[i] = out[i - 1];
                    i -= 1;
                }
                key[i] = k;
                out[i] = v;
            }
        }
        nc
    }

    /// Assign `l` at level 1 and propagate. Returns conflict clause or NIL.
    fn probe_one(&mut self, l: Lit) -> u32 {
        self.new_level();
        self.enqueue(l, NIL);
        self.stats.probes += 1;
        self.propagate()
    }

    fn bump_clause_vars(&mut self, c: u32) {
        let h = at(&self.hdr, c as usize);
        for k in h.start as usize..(h.start + h.len) as usize {
            let v = at(&self.lits, k).var();
            self.bump_var(v);
        }
    }

    /// Assert a root fact discovered by probing.
    fn probe_assert(&mut self, l: Lit) -> Root {
        match self.value(l) {
            V_TRUE => Root::Ok,
            V_FALSE => Root::Conflict,
            _ => {
                self.enqueue(l, NIL);
                if self.propagate() != NIL {
                    Root::Conflict
                } else {
                    Root::Ok
                }
            }
        }
    }

    pub(crate) fn probe(&mut self, prop_budget: u64, ticker: &mut Ticker) -> ProbeOutcome {
        self.backtrack(0);
        let mut res = ProbeOutcome { fixed: 0, failed: 0, root: Root::Ok };
        if self.propagate() != NIL {
            res.root = Root::Conflict;
            return res;
        }
        let root0 = self.hot.trail_len;
        let mut cand = [0u32; PROBE_K];
        let nc = self.select_probe_candidates(&mut cand);
        let p0 = self.stats.propagations;
        let mut last = p0;
        for &v in cand.iter().take(nc) {
            let now_p = self.stats.propagations;
            let units = work_units(now_p - last);
            last = now_p;
            if now_p - p0 > prop_budget || ticker.tick_n(units) {
                break;
            }
            if self.is_assigned(v) {
                continue;
            }
            let pos = Lit::new(v, false);
            let neg = !pos;
            // ---- v = true ----
            let gen = self.next_stamp();
            let confl = self.probe_one(pos);
            if confl != NIL {
                self.bump_clause_vars(confl);
                self.backtrack(0);
                res.failed += 1;
                self.stats.failed_lits += 1;
                if self.probe_assert(neg) == Root::Conflict {
                    res.root = Root::Conflict;
                    return res;
                }
                continue;
            }
            let lim = at(&self.trail_lim, 0) as usize;
            for i in lim + 1..self.hot.trail_len as usize {
                let l = at(&self.trail, i);
                *at_mut(&mut self.lit_stamp, l.idx()) = gen;
            }
            self.backtrack(0);
            // ---- v = false ----
            let confl = self.probe_one(neg);
            if confl != NIL {
                self.bump_clause_vars(confl);
                self.backtrack(0);
                res.failed += 1;
                self.stats.failed_lits += 1;
                if self.probe_assert(pos) == Root::Conflict {
                    res.root = Root::Conflict;
                    return res;
                }
                continue;
            }
            // literals implied by both polarities
            let lim = at(&self.trail_lim, 0) as usize;
            let mut nboth = 0usize;
            for i in lim + 1..self.hot.trail_len as usize {
                let l = at(&self.trail, i);
                if at(&self.lit_stamp, l.idx()) == gen {
                    *at_mut(&mut self.clear_buf, nboth) = l;
                    nboth += 1;
                }
            }
            self.backtrack(0);
            for i in 0..nboth {
                let l = at(&self.clear_buf, i);
                if self.probe_assert(l) == Root::Conflict {
                    res.root = Root::Conflict;
                    return res;
                }
            }
            if nboth == 0 {
                let p = at_mut(&mut self.probe_penalty, v as usize);
                *p = (*p + 1).min(7);
            }
        }
        res.fixed = self.hot.trail_len - root0;
        res
    }
}
