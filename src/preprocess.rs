//! Module 6: repeatable lightweight pre-/in-processing, all at level 0 and
//! allocation-free:
//! * iterative unit propagation + root simplification (`root_simplify_and_rebuild`);
//! * pure literal elimination (satisfiability-preserving; counts are taken over
//!   every live *original* clause, masked or not);
//! * backward subsumption with 64-bit variable signatures as a bitwise
//!   pre-filter, then exact check via literal stamps, bounded by a work budget.

use crate::arena::SolverWorkspace;
use crate::propagate::Root;
use crate::types::*;
use crate::util::*;

#[derive(Copy, Clone, Debug, Default)]
pub struct PreStats {
    pub fixed: u32,
    pub subsumed: u32,
    pub pure: u32,
}

#[inline(always)]
fn var_sig(v: Var) -> u64 {
    1u64 << (v.wrapping_mul(0x9E37_79B1) >> 26)
}

impl SolverWorkspace {
    /// Pure literal elimination. Returns the number of literals fixed.
    pub(crate) fn pure_literal_pass(&mut self) -> u32 {
        debug_assert_eq!(self.hot.dlevel, 0);
        self.lit_count.fill(0);
        for c in 0..self.n_orig as usize {
            let h = at(&self.hdr, c);
            if h.flags & F_DELETED != 0 {
                continue;
            }
            let s = h.start as usize;
            let e = s + h.len as usize;
            let mut sat = false;
            for k in s..e {
                if self.value(at(&self.lits, k)) == V_TRUE {
                    sat = true;
                    break;
                }
            }
            if sat {
                continue;
            }
            for k in s..e {
                let l = at(&self.lits, k);
                if self.value(l) == V_UNDEF {
                    *at_mut(&mut self.lit_count, l.idx()) += 1;
                }
            }
        }
        let mut fixed = 0;
        for v in 0..self.n_vars {
            if self.is_assigned(v) {
                continue;
            }
            let p = at(&self.lit_count, (v as usize) << 1);
            let n = at(&self.lit_count, ((v as usize) << 1) | 1);
            if (p > 0) != (n > 0) {
                self.enqueue(Lit::new(v, n > 0), NIL);
                fixed += 1;
            }
        }
        self.stats.pure += fixed as u64;
        fixed
    }

    /// Backward subsumption over live original clauses (requires a fresh
    /// `root_simplify_and_rebuild`, so all remaining literals are unassigned).
    pub(crate) fn subsumption_pass(&mut self, mut budget: i64) -> u32 {
        debug_assert_eq!(self.hot.dlevel, 0);
        let n = self.n_orig as usize;
        for c in 0..n {
            let h = at(&self.hdr, c);
            let mut s = 0u64;
            if h.flags & F_DELETED == 0 {
                for k in h.start as usize..(h.start + h.len) as usize {
                    s |= var_sig(at(&self.lits, k).var());
                }
            }
            *at_mut(&mut self.sig, c) = s;
        }
        let mut removed = 0u32;
        for c in 0..n {
            if budget <= 0 {
                break;
            }
            let hc = at(&self.hdr, c);
            if hc.flags & F_DELETED != 0 || hc.len < 2 {
                continue;
            }
            let cs = hc.start as usize;
            let ce = cs + hc.len as usize;
            // literal with the shortest occurrence list
            let mut best_l = at(&self.lits, cs);
            let mut best_n = usize::MAX;
            for k in cs..ce {
                let l = at(&self.lits, k);
                let (os, oe) = self.occ_range(l);
                if oe - os < best_n {
                    best_n = oe - os;
                    best_l = l;
                }
            }
            let sc = at(&self.sig, c);
            let (os, oe) = self.occ_range(best_l);
            for i in os..oe {
                let d = at(&self.occ, i) as usize;
                if d == c {
                    continue;
                }
                let hd = at(&self.hdr, d);
                if hd.flags & F_DELETED != 0 || hd.len < hc.len {
                    continue;
                }
                budget -= 1;
                if sc & !at(&self.sig, d) != 0 {
                    continue; // bitwise reject
                }
                budget -= hd.len as i64;
                let g = self.next_stamp();
                for k in hd.start as usize..(hd.start + hd.len) as usize {
                    let l = at(&self.lits, k);
                    *at_mut(&mut self.lit_stamp, l.idx()) = g;
                }
                let mut all = true;
                for k in cs..ce {
                    if at(&self.lit_stamp, at(&self.lits, k).idx()) != g {
                        all = false;
                        break;
                    }
                }
                if all {
                    at_mut(&mut self.hdr, d).flags |= F_DELETED;
                    removed += 1;
                }
            }
        }
        self.stats.subsumed += removed as u64;
        removed
    }

    /// Full preprocessing: `rounds` × (UP + simplify, pure literals, subsumption).
    pub(crate) fn preprocess(&mut self, rounds: u32) -> (Root, PreStats) {
        self.backtrack(0);
        let mut st = PreStats::default();
        let root0 = self.hot.trail_len;
        for _ in 0..rounds {
            if self.root_simplify_and_rebuild() == Root::Conflict {
                return (Root::Conflict, st);
            }
            let p = self.pure_literal_pass();
            st.pure += p;
            if p > 0 && self.root_simplify_and_rebuild() == Root::Conflict {
                return (Root::Conflict, st);
            }
            let budget = (self.layout.orig_lits as i64 * 8).max(1 << 16);
            let s = self.subsumption_pass(budget);
            st.subsumed += s;
            if p == 0 && s == 0 {
                break;
            }
        }
        st.fixed = self.hot.trail_len - root0;
        (Root::Ok, st)
    }

    /// Cheap in-processing round (tier change / major restart).
    pub(crate) fn inprocess(&mut self) -> Root {
        self.backtrack(0);
        if self.root_simplify_and_rebuild() == Root::Conflict {
            return Root::Conflict;
        }
        if self.pure_literal_pass() > 0 && self.root_simplify_and_rebuild() == Root::Conflict {
            return Root::Conflict;
        }
        let budget = (self.layout.orig_lits as i64).max(1 << 14);
        self.subsumption_pass(budget);
        Root::Ok
    }
}
