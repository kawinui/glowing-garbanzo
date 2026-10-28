//! Allocation-free primitives: unchecked indexing, cache-line-aligned bit
//! vectors with popcount, XorShift64* PRNG, low-overhead deadline ticker and
//! the fixed-capacity event ring buffer.

use crate::types::{Event, EventKind};
use std::time::Instant;

// ---------------------------------------------------------------------------
// Unchecked indexing.
//
// Invariant (established once, at load time, by `SolverWorkspace::new`):
// every literal stored in any arena is `< 2 * n_vars`, every clause id is
// `< n_orig + learnt_clause_cap`, every arena range lies inside its arena,
// and every trail position is `< n_vars`. All hot-loop indices are derived
// from those values, so the bounds checks are provably redundant.
// Debug builds (and the `checked` feature) keep the checks.
// ---------------------------------------------------------------------------

#[inline(always)]
pub(crate) fn at<T: Copy>(s: &[T], i: usize) -> T {
    #[cfg(feature = "checked")]
    {
        s[i]
    }
    #[cfg(not(feature = "checked"))]
    {
        debug_assert!(i < s.len(), "index {i} >= len {}", s.len());
        // SAFETY: see module invariant above.
        unsafe { *s.get_unchecked(i) }
    }
}

#[inline(always)]
pub(crate) fn at_mut<T>(s: &mut [T], i: usize) -> &mut T {
    #[cfg(feature = "checked")]
    {
        &mut s[i]
    }
    #[cfg(not(feature = "checked"))]
    {
        debug_assert!(i < s.len(), "index {i} >= len {}", s.len());
        // SAFETY: see module invariant above.
        unsafe { s.get_unchecked_mut(i) }
    }
}

/// Boxed slice allocated once (load time only).
pub(crate) fn boxed<T: Clone>(n: usize, v: T) -> Box<[T]> {
    vec![v; n].into_boxed_slice()
}

// ---------------------------------------------------------------------------
// Cache-line aligned bit vector.
// ---------------------------------------------------------------------------

/// One 64-byte cache line = 512 bits.
#[repr(C, align(64))]
#[derive(Copy, Clone)]
pub struct Line(pub [u64; 8]);

pub struct BitSet {
    lines: Box<[Line]>,
    nbits: usize,
}

impl BitSet {
    pub fn new(nbits: usize) -> Self {
        let n = nbits.div_ceil(512).max(1);
        BitSet { lines: boxed(n, Line([0; 8])), nbits }
    }
    pub const fn bytes_for(nbits: usize) -> usize {
        let l = nbits.div_ceil(512);
        (if l == 0 { 1 } else { l }) * 64
    }
    #[inline(always)]
    pub fn len(&self) -> usize {
        self.nbits
    }
    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        self.nbits == 0
    }
    #[inline(always)]
    pub fn words(&self) -> &[u64] {
        // SAFETY: Line is repr(C) [u64; 8] with no padding (size 64, align 64).
        unsafe { core::slice::from_raw_parts(self.lines.as_ptr() as *const u64, self.lines.len() * 8) }
    }
    #[inline(always)]
    pub fn words_mut(&mut self) -> &mut [u64] {
        // SAFETY: as above, unique borrow.
        unsafe {
            core::slice::from_raw_parts_mut(self.lines.as_mut_ptr() as *mut u64, self.lines.len() * 8)
        }
    }
    #[inline(always)]
    pub fn get(&self, i: usize) -> bool {
        (at(self.words(), i >> 6) >> (i & 63)) & 1 != 0
    }
    #[inline(always)]
    pub fn set(&mut self, i: usize) {
        *at_mut(self.words_mut(), i >> 6) |= 1u64 << (i & 63);
    }
    #[inline(always)]
    pub fn clear(&mut self, i: usize) {
        *at_mut(self.words_mut(), i >> 6) &= !(1u64 << (i & 63));
    }
    #[inline(always)]
    pub fn toggle(&mut self, i: usize) {
        *at_mut(self.words_mut(), i >> 6) ^= 1u64 << (i & 63);
    }
    /// Branch-free assign.
    #[inline(always)]
    pub fn assign(&mut self, i: usize, b: bool) {
        let m = 1u64 << (i & 63);
        let w = at_mut(self.words_mut(), i >> 6);
        *w = (*w & !m) | ((b as u64).wrapping_neg() & m);
    }
    pub fn clear_all(&mut self) {
        self.words_mut().fill(0);
    }
    /// Set bits `0..nbits` (tail bits stay zero so popcounts are exact).
    pub fn set_all(&mut self) {
        let n = self.nbits;
        let w = self.words_mut();
        w.fill(0);
        let full = n >> 6;
        w[..full].fill(u64::MAX);
        if n & 63 != 0 {
            w[full] = (1u64 << (n & 63)) - 1;
        }
    }
    /// Hardware popcount over the whole set.
    #[inline]
    pub fn count_ones(&self) -> u32 {
        self.words().iter().map(|w| w.count_ones()).sum()
    }
    /// popcount(self & other)
    #[inline]
    pub fn count_and(&self, other: &BitSet) -> u32 {
        self.words().iter().zip(other.words()).map(|(a, b)| (a & b).count_ones()).sum()
    }
    /// Fast slice copy (memcpy of whole cache lines).
    #[inline]
    pub fn copy_from(&mut self, other: &BitSet) {
        self.words_mut().copy_from_slice(other.words());
    }
    pub fn fill_random(&mut self, rng: &mut Rng) {
        let n = self.nbits;
        for w in self.words_mut() {
            *w = rng.next_u64();
        }
        // keep tail zero
        let w = self.words_mut();
        let full = n >> 6;
        if n & 63 != 0 {
            w[full] &= (1u64 << (n & 63)) - 1;
            for x in &mut w[full + 1..] {
                *x = 0;
            }
        } else {
            for x in &mut w[full..] {
                *x = 0;
            }
        }
    }
}

// ---------------------------------------------------------------------------
// XorShift64* PRNG (Vigna). 1 multiply, 3 shifts, no state beyond a u64.
// ---------------------------------------------------------------------------

#[derive(Copy, Clone, Debug)]
pub struct Rng(u64);

impl Rng {
    pub fn new(seed: u64) -> Self {
        // splitmix64 scramble so nearby seeds diverge immediately
        let mut z = seed.wrapping_add(0x9E37_79B9_7F4A_7C15);
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^= z >> 31;
        Rng(z | 1)
    }
    #[inline(always)]
    pub fn next_u64(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }
    #[inline(always)]
    pub fn next_u32(&mut self) -> u32 {
        (self.next_u64() >> 32) as u32
    }
    /// Uniform in `0..n` (Lemire multiply-shift, n > 0).
    #[inline(always)]
    pub fn below(&mut self, n: u32) -> u32 {
        ((self.next_u32() as u64 * n as u64) >> 32) as u32
    }
    /// True with probability `p` ∈ [0,1].
    #[inline(always)]
    pub fn chance(&mut self, p: f32) -> bool {
        self.next_f32() < p
    }
    #[inline(always)]
    pub fn next_f32(&mut self) -> f32 {
        (self.next_u32() >> 8) as f32 * (1.0 / 16_777_216.0)
    }
}

// ---------------------------------------------------------------------------
// Deadline ticker: reads the clock only every `period` ticks.
// ---------------------------------------------------------------------------

/// True once `t` has been reached. Never call from `propagate()`.
#[inline]
pub(crate) fn past(t: Instant) -> bool {
    Instant::now() >= t
}

/// Ticker units for a step that propagated `dprops` literals: `1 + dprops / 64`.
#[inline(always)]
pub(crate) fn work_units(dprops: u64) -> i32 {
    1 + (dprops >> 6).min(1 << 20) as i32
}

pub struct Ticker {
    end: Instant,
    countdown: i32,
    period: i32,
    pub expired: bool,
}

impl Ticker {
    pub fn new(end: Instant, period: i32) -> Self {
        Ticker { end, countdown: period, period, expired: Instant::now() >= end }
    }
    #[inline(always)]
    pub fn tick(&mut self) -> bool {
        self.tick_n(1)
    }
    /// Account `units` of work (a step that cost more than one tick); the
    /// clock is read whenever the accumulated work crosses `period`.
    #[inline(always)]
    pub fn tick_n(&mut self, units: i32) -> bool {
        self.countdown -= units;
        if self.countdown <= 0 {
            self.countdown = self.period;
            if Instant::now() >= self.end {
                self.expired = true;
            }
        }
        self.expired
    }
}

// ---------------------------------------------------------------------------
// Fixed-capacity ring-buffer event log (overwrites oldest).
// ---------------------------------------------------------------------------

pub const LOG_CAP: usize = 2048;

pub struct EventLog {
    buf: Box<[Event]>,
    head: usize,
    len: usize,
    pub dropped: u64,
}

impl EventLog {
    pub fn new() -> Self {
        EventLog {
            buf: boxed(LOG_CAP, Event { t_us: 0, epoch: 0, kind: EventKind::Timeout }),
            head: 0,
            len: 0,
            dropped: 0,
        }
    }
    pub const fn bytes() -> usize {
        LOG_CAP * core::mem::size_of::<Event>()
    }
    #[inline]
    pub fn push(&mut self, e: Event) {
        let cap = self.buf.len();
        if self.len < cap {
            self.buf[(self.head + self.len) % cap] = e;
            self.len += 1;
        } else {
            self.buf[self.head] = e;
            self.head = (self.head + 1) % cap;
            self.dropped += 1;
        }
    }
    pub fn clear(&mut self) {
        self.head = 0;
        self.len = 0;
        self.dropped = 0;
    }
    pub fn iter(&self) -> impl Iterator<Item = &Event> + '_ {
        let cap = self.buf.len();
        (0..self.len).map(move |i| &self.buf[(self.head + i) % cap])
    }
}

impl Default for EventLog {
    fn default() -> Self {
        Self::new()
    }
}
