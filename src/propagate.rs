//! Two-watched-literal unit propagation over intrusive, fixed-capacity watch
//! lists (one node per clause watch, relinked in O(1) — no `Vec` per literal,
//! so moving a watch can never reallocate), trail management, and the
//! root-level simplify + watch-rebuild pass that every in-processing step,
//! clause-DB reduction and relaxation change goes through.

use crate::arena::SolverWorkspace;
use crate::types::*;
use crate::util::*;

/// Outcome of a root-level pass.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum Root {
    Ok,
    Conflict,
}

impl SolverWorkspace {
    #[inline(always)]
    pub(crate) fn value(&self, l: Lit) -> i8 {
        at(&self.val, l.idx())
    }

    #[inline(always)]
    pub(crate) fn is_assigned(&self, v: Var) -> bool {
        at(&self.val, (v as usize) << 1) != V_UNDEF
    }

    #[inline(always)]
    pub(crate) fn enqueue(&mut self, l: Lit, reason: u32) {
        debug_assert_eq!(self.value(l), V_UNDEF);
        let v = l.var() as usize;
        *at_mut(&mut self.val, l.idx()) = V_TRUE;
        *at_mut(&mut self.val, (!l).idx()) = V_FALSE;
        *at_mut(&mut self.level, v) = self.hot.dlevel;
        *at_mut(&mut self.reason, v) = reason;
        *at_mut(&mut self.trail, self.hot.trail_len as usize) = l;
        self.hot.trail_len += 1;
    }

    #[inline(always)]
    pub(crate) fn new_level(&mut self) {
        *at_mut(&mut self.trail_lim, self.hot.dlevel as usize) = self.hot.trail_len;
        self.hot.dlevel += 1;
    }

    /// Number of root-level (permanently fixed) assignments.
    #[inline]
    pub(crate) fn root_len(&self) -> u32 {
        if self.hot.dlevel == 0 {
            self.hot.trail_len
        } else {
            at(&self.trail_lim, 0)
        }
    }

    /// Undo to `lvl`, saving phases and re-inserting variables into the order tree.
    pub(crate) fn backtrack(&mut self, lvl: u32) {
        if self.hot.dlevel <= lvl {
            return;
        }
        let lim = at(&self.trail_lim, lvl as usize);
        let mut i = self.hot.trail_len;
        while i > lim {
            i -= 1;
            let l = at(&self.trail, i as usize);
            let v = l.var();
            self.phase.assign(v as usize, !l.is_neg());
            *at_mut(&mut self.val, l.idx()) = V_UNDEF;
            *at_mut(&mut self.val, (!l).idx()) = V_UNDEF;
            *at_mut(&mut self.reason, v as usize) = NIL;
            self.order_insert(v);
        }
        self.hot.trail_len = lim;
        self.hot.qhead = lim;
        self.hot.dlevel = lvl;
    }

    #[inline(always)]
    pub(crate) fn attach(&mut self, c: u32) {
        let h = at(&self.hdr, c as usize);
        debug_assert!(h.len >= 2);
        let s = h.start as usize;
        let l0 = at(&self.lits, s);
        let l1 = at(&self.lits, s + 1);
        let n0 = 2 * c;
        let n1 = n0 + 1;
        *at_mut(&mut self.wnode, n0 as usize) = WatchNode { next: at(&self.whead, l0.idx()), blocker: l1 };
        *at_mut(&mut self.whead, l0.idx()) = n0;
        *at_mut(&mut self.wnode, n1 as usize) = WatchNode { next: at(&self.whead, l1.idx()), blocker: l0 };
        *at_mut(&mut self.whead, l1.idx()) = n1;
    }

    /// Unit propagation. Returns the conflicting clause id or `NIL`.
    ///
    /// Masked (relaxed-away) original clauses are skipped; their watches are
    /// left untouched and are rebuilt whenever clauses are unmasked.
    pub(crate) fn propagate(&mut self) -> u32 {
        let n_orig = self.n_orig;
        let all_active = self.hot.all_active;
        while self.hot.qhead < self.hot.trail_len {
            let p = at(&self.trail, self.hot.qhead as usize);
            self.hot.qhead += 1;
            self.stats.propagations += 1;
            let fl = !p; // literal that just became false
            let mut prev = NIL;
            let mut cur = at(&self.whead, fl.idx());
            while cur != NIL {
                let node = at(&self.wnode, cur as usize);
                let next = node.next;
                if self.value(node.blocker) == V_TRUE {
                    prev = cur;
                    cur = next;
                    continue;
                }
                let c = cur >> 1;
                let w = (cur & 1) as usize;
                let h = at(&self.hdr, c as usize);
                if h.flags & F_DELETED != 0 {
                    // lazy unlink of dead watches
                    if prev == NIL {
                        *at_mut(&mut self.whead, fl.idx()) = next;
                    } else {
                        at_mut(&mut self.wnode, prev as usize).next = next;
                    }
                    cur = next;
                    continue;
                }
                if !all_active && c < n_orig && !self.active.get(c as usize) {
                    prev = cur;
                    cur = next;
                    continue;
                }
                let s = h.start as usize;
                debug_assert_eq!(at(&self.lits, s + w), fl);
                let other = at(&self.lits, s + (1 - w));
                if self.value(other) == V_TRUE {
                    at_mut(&mut self.wnode, cur as usize).blocker = other;
                    prev = cur;
                    cur = next;
                    continue;
                }
                // look for a replacement watch
                let end = s + h.len as usize;
                let mut k = s + 2;
                let mut moved = false;
                while k < end {
                    let lk = at(&self.lits, k);
                    if self.value(lk) != V_FALSE {
                        *at_mut(&mut self.lits, s + w) = lk;
                        *at_mut(&mut self.lits, k) = fl;
                        if prev == NIL {
                            *at_mut(&mut self.whead, fl.idx()) = next;
                        } else {
                            at_mut(&mut self.wnode, prev as usize).next = next;
                        }
                        let head = at(&self.whead, lk.idx());
                        *at_mut(&mut self.wnode, cur as usize) = WatchNode { next: head, blocker: other };
                        *at_mut(&mut self.whead, lk.idx()) = cur;
                        moved = true;
                        break;
                    }
                    k += 1;
                }
                if moved {
                    cur = next;
                    continue;
                }
                at_mut(&mut self.wnode, cur as usize).blocker = other;
                if self.value(other) == V_FALSE {
                    self.hot.qhead = self.hot.trail_len;
                    return c;
                }
                self.enqueue(other, c);
                prev = cur;
                cur = next;
            }
        }
        NIL
    }

    /// Level-0 simplification + full watch rebuild:
    /// * deletes root-satisfied clauses, strips root-false literals in place
    ///   (working arena only — the pristine copy is never touched);
    /// * enqueues new root units; detects all-false (active) clauses;
    /// * re-attaches every surviving clause, then propagates to fixpoint.
    pub(crate) fn root_simplify_and_rebuild(&mut self) -> Root {
        debug_assert_eq!(self.hot.dlevel, 0);
        for i in 0..self.hot.trail_len as usize {
            let v = at(&self.trail, i).var();
            *at_mut(&mut self.reason, v as usize) = NIL;
        }
        self.whead.fill(NIL);
        let total = self.n_orig + self.hot.num_learnt;
        let mut conflict = false;
        for c in 0..total {
            let h = at(&self.hdr, c as usize);
            if h.flags & F_DELETED != 0 {
                continue;
            }
            let s = h.start as usize;
            let e = s + h.len as usize;
            let mut j = s;
            let mut sat = false;
            for k in s..e {
                let l = at(&self.lits, k);
                let v = self.value(l);
                if v == V_TRUE {
                    sat = true;
                    break;
                }
                if v == V_UNDEF {
                    *at_mut(&mut self.lits, j) = l;
                    j += 1;
                }
            }
            if sat {
                at_mut(&mut self.hdr, c as usize).flags |= F_DELETED;
                continue;
            }
            let len = (j - s) as u32;
            at_mut(&mut self.hdr, c as usize).len = len;
            let is_active = c >= self.n_orig || self.hot.all_active || self.active.get(c as usize);
            match len {
                0 => {
                    if is_active {
                        conflict = true;
                    }
                }
                1 => {
                    if is_active {
                        let u = at(&self.lits, s);
                        if self.value(u) == V_UNDEF {
                            self.enqueue(u, NIL);
                        } else if self.value(u) == V_FALSE {
                            conflict = true;
                        }
                        at_mut(&mut self.hdr, c as usize).flags |= F_DELETED;
                    }
                }
                _ => self.attach(c),
            }
        }
        #[cfg(debug_assertions)]
        self.check_watches("after-rebuild");
        if conflict || self.propagate() != NIL {
            return Root::Conflict;
        }
        Root::Ok
    }
}

#[cfg(debug_assertions)]
impl SolverWorkspace {
    /// Debug-only: every reachable watch node must watch the literal whose list it is in.
    #[allow(dead_code)]
    pub(crate) fn check_watches(&self, tag: &str) {
        for l in 0..self.whead.len() {
            let mut cur = self.whead[l];
            let mut steps = 0;
            while cur != NIL {
                let c = (cur >> 1) as usize;
                let h = self.hdr[c];
                if h.flags & F_DELETED == 0 {
                    let w = (cur & 1) as usize;
                    assert!(h.len >= 2, "{tag}: watched clause {c} len {}", h.len);
                    assert_eq!(self.lits[h.start as usize + w].idx(), l, "{tag}: clause {c} node {cur} learnt={}", h.flags & F_LEARNT);
                }
                cur = self.wnode[cur as usize].next;
                steps += 1;
                assert!(steps < 100_000_000);
            }
        }
    }
}
