//! Module 4: zero-overhead adaptive variable ordering.
//!
//! Scores live in a flat `[u32; n_vars]`. Instead of a VSIDS binary heap the
//! decision queue is a flat segment ("tournament") tree of `2P` u32 slots:
//! leaves hold the variable id (or NIL when removed), internal nodes hold the
//! id of the max-score variable in their subtree. Bump / insert / remove walk
//! one leaf-to-root path and stop early as soon as a node's winner is
//! unaffected — no swaps, no allocation, fully iterative.
//!
//! Decay is *bitwise*: the bump increment doubles every `decay_interval`
//! conflicts (equivalent to halving every score), and when it grows large
//! all scores are shifted right in one pass (`score >>= SHIFT`) and the tree is
//! rebuilt. That makes the O(n) pass amortised over ~`SHIFT * interval`
//! conflicts.

use crate::arena::SolverWorkspace;
use crate::types::*;
use crate::util::*;

const INC_LIMIT: u32 = 1 << 24;
const SCORE_LIMIT: u32 = 1 << 30;
const SHIFT: u32 = 18;

impl SolverWorkspace {
    #[inline(always)]
    fn better(&self, a: u32, b: u32) -> u32 {
        if a == NIL {
            return b;
        }
        if b == NIL {
            return a;
        }
        if at(&self.score, b as usize) > at(&self.score, a as usize) {
            b
        } else {
            a
        }
    }

    /// Rebuild all internal nodes bottom-up (leaves untouched).
    pub(crate) fn order_rebuild(&mut self) {
        let p = self.leaves as usize;
        let mut j = p - 1;
        while j >= 1 {
            let w = self.better(at(&self.tree, 2 * j), at(&self.tree, 2 * j + 1));
            *at_mut(&mut self.tree, j) = w;
            j -= 1;
        }
    }

    pub(crate) fn order_init(&mut self) {
        let p = self.leaves as usize;
        self.tree.fill(NIL);
        for v in 0..self.n_vars as usize {
            self.tree[p + v] = v as u32;
        }
        if p > 1 {
            self.order_rebuild();
        } else {
            self.tree[1] = if self.n_vars > 0 { 0 } else { NIL };
            // p == 1: leaf index 1 is the root
        }
    }

    /// Re-evaluate the path above leaf of `v`. Early exit once the winner at a
    /// node is unchanged and is not `v` itself (then no ancestor can change).
    #[inline]
    fn order_fix(&mut self, v: u32) {
        let mut j = (self.leaves + v) as usize >> 1;
        while j >= 1 {
            let old = at(&self.tree, j);
            let w = self.better(at(&self.tree, 2 * j), at(&self.tree, 2 * j + 1));
            if w == old && old != v {
                return;
            }
            *at_mut(&mut self.tree, j) = w;
            j >>= 1;
        }
    }

    #[inline]
    pub(crate) fn order_insert(&mut self, v: u32) {
        let leaf = (self.leaves + v) as usize;
        if at(&self.tree, leaf) != NIL {
            return;
        }
        *at_mut(&mut self.tree, leaf) = v;
        if self.leaves > 1 {
            self.order_fix(v);
        }
    }

    #[inline]
    fn order_remove(&mut self, v: u32) {
        let leaf = (self.leaves + v) as usize;
        *at_mut(&mut self.tree, leaf) = NIL;
        if self.leaves > 1 {
            self.order_fix(v);
        }
    }

    /// Conflict participation bump.
    #[inline]
    pub(crate) fn bump_var(&mut self, v: u32) {
        let s = at_mut(&mut self.score, v as usize);
        *s = s.saturating_add(self.hot.inc);
        if *s >= SCORE_LIMIT {
            self.rescale_scores();
        } else if self.leaves > 1 && at(&self.tree, (self.leaves + v) as usize) != NIL {
            self.order_fix(v);
        }
    }

    /// Raw bump without tree maintenance (batch updates; call `order_rebuild` after).
    #[inline(always)]
    pub(crate) fn bump_raw(&mut self, v: u32, amount: u32) {
        let s = at_mut(&mut self.score, v as usize);
        *s = s.saturating_add(amount).min(SCORE_LIMIT - 1);
    }

    /// Per-conflict decay bookkeeping.
    #[inline]
    pub(crate) fn decay_tick(&mut self) {
        self.hot.since_decay += 1;
        if self.hot.since_decay >= self.hot.decay_interval {
            self.hot.since_decay = 0;
            self.hot.inc <<= 1;
            if self.hot.inc >= INC_LIMIT {
                self.rescale_scores();
            }
        }
    }

    /// Bitwise decay of every score + rebuild.
    pub(crate) fn rescale_scores(&mut self) {
        for s in self.score.iter_mut() {
            *s >>= SHIFT;
        }
        self.hot.inc = (self.hot.inc >> SHIFT).max(1);
        if self.leaves > 1 {
            self.order_rebuild();
        }
    }

    /// Random low-bit perturbation for multi-seed tie-breaking.
    pub(crate) fn perturb_scores(&mut self) {
        for i in 0..self.n_vars as usize {
            let r = self.rng.next_u32() & 7;
            let s = at_mut(&mut self.score, i);
            *s = (*s & !7) | r;
        }
        if self.leaves > 1 {
            self.order_rebuild();
        }
    }

    /// Highest-score unassigned variable, lazily discarding assigned ones.
    #[inline]
    pub(crate) fn pick_branch(&mut self) -> u32 {
        if self.leaves == 1 {
            // single variable
            return if self.n_vars == 1 && !self.is_assigned(0) { 0 } else { NIL };
        }
        loop {
            let v = at(&self.tree, 1);
            if v == NIL {
                return NIL;
            }
            if !self.is_assigned(v) {
                return v;
            }
            self.order_remove(v);
        }
    }
}
