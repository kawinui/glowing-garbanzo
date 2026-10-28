//! Integration tests: soundness vs brute force, zero allocation inside
//! `solve()`, memory-budget enforcement, anytime UNKNOWN results, edge cases.

use std::alloc::{GlobalAlloc, Layout, System};
use std::cell::Cell;
use zsat::*;

// Per-thread counting allocator (tests run in parallel threads).
struct Counting;
thread_local! {
    static ARMED: Cell<bool> = const { Cell::new(false) };
    static COUNT: Cell<u64> = const { Cell::new(0) };
}
fn note() {
    let _ = ARMED.try_with(|a| {
        if a.get() {
            let _ = COUNT.try_with(|c| c.set(c.get() + 1));
        }
    });
}
unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, l: Layout) -> *mut u8 {
        note();
        System.alloc(l)
    }
    unsafe fn alloc_zeroed(&self, l: Layout) -> *mut u8 {
        note();
        System.alloc_zeroed(l)
    }
    unsafe fn dealloc(&self, p: *mut u8, l: Layout) {
        System.dealloc(p, l)
    }
    unsafe fn realloc(&self, p: *mut u8, l: Layout, n: usize) -> *mut u8 {
        note();
        System.realloc(p, l, n)
    }
}
#[global_allocator]
static A: Counting = Counting;

fn solve_counting(s: &mut Solver) -> (Status, u64) {
    COUNT.with(|c| c.set(0));
    ARMED.with(|a| a.set(true));
    let st = s.solve();
    ARMED.with(|a| a.set(false));
    (st, COUNT.with(|c| c.get()))
}

struct Gen(u64);
impl Gen {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
}

fn random_ksat(n: u32, m: u32, k: u32, seed: u64) -> Formula {
    let mut g = Gen(seed | 1);
    let mut f = Formula::new(n);
    for _ in 0..m {
        let mut c: Vec<i32> = Vec::new();
        while c.len() < k as usize {
            let v = (g.next() % n as u64) as i32 + 1;
            if !c.iter().any(|x| x.abs() == v) {
                c.push(if g.next() & 1 == 0 { v } else { -v });
            }
        }
        f.add_clause(&c);
    }
    f
}

fn violated(f: &Formula, val: impl Fn(u32) -> bool) -> usize {
    (0..f.num_clauses()).filter(|&i| !f.clause(i).iter().any(|l| val(l.var()) != l.is_neg())).count()
}

fn brute(f: &Formula) -> bool {
    (0u32..1 << f.num_vars).any(|a| violated(f, |v| a >> v & 1 == 1) == 0)
}

fn pigeonhole(p: u32, h: u32) -> Formula {
    let var = |i: u32, j: u32| (i * h + j + 1) as i32;
    let mut f = Formula::new(p * h);
    for i in 0..p {
        f.add_clause(&(0..h).map(|j| var(i, j)).collect::<Vec<_>>());
    }
    for j in 0..h {
        for a in 0..p {
            for b in a + 1..p {
                f.add_clause(&[-var(a, j), -var(b, j)]);
            }
        }
    }
    f
}

fn cfg(ms: u64) -> Config {
    Config { timeout_ms: ms, memory_budget: 32 << 20, ..Config::default() }
}

#[test]
fn agrees_with_brute_force_and_never_allocates() {
    let mut g = Gen(0xABCDEF);
    for i in 0..400 {
        let n = 3 + (g.next() % 10) as u32;
        let k = 2 + (g.next() % 2) as u32;
        let m = n * (2 + (g.next() % 5) as u32);
        let f = random_ksat(n, m, k, g.next());
        let truth = brute(&f);
        for (relax, learning) in [(true, true), (false, false)] {
            let c = Config { relaxation: relax, learning, seed: g.next(), ..cfg(3000) };
            let mut s = Solver::new(&f, c).unwrap();
            let (st, allocs) = solve_counting(&mut s);
            assert_eq!(allocs, 0, "instance {i}: allocated inside solve()");
            match st {
                Status::Sat => {
                    assert!(truth, "instance {i}: SAT claimed on UNSAT formula");
                    assert_eq!(violated(&f, |v| s.model_value(v)), 0, "instance {i}: bad model");
                    assert!(s.is_strict(), "SAT must be reported in strict mode");
                }
                Status::Unsat => {
                    assert!(!truth, "instance {i}: UNSAT claimed on SAT formula");
                    assert!(s.is_strict(), "UNSAT must be reported in strict mode");
                }
                Status::Unknown => panic!("instance {i}: unknown on a tiny formula"),
            }
        }
    }
}

#[test]
fn proves_pigeonhole_unsat() {
    let f = pigeonhole(7, 6);
    let mut s = Solver::new(&f, cfg(20_000)).unwrap();
    let (st, allocs) = solve_counting(&mut s);
    assert_eq!(st, Status::Unsat);
    assert_eq!(allocs, 0);
    assert_eq!(s.ctrl.mode, Mode::Conservative);
}

#[test]
fn solves_large_random_sat_without_allocating() {
    let f = random_ksat(20_000, 76_000, 3, 99); // ratio 3.8
    let mut s = Solver::new(&f, Config { timeout_ms: 20_000, ..Config::default() }).unwrap();
    let (st, allocs) = solve_counting(&mut s);
    assert_eq!(allocs, 0);
    assert_eq!(st, Status::Sat);
    assert_eq!(violated(&f, |v| s.model_value(v)), 0);
}

#[test]
fn timeout_returns_unknown_with_consistent_best_so_far() {
    let f = pigeonhole(11, 10); // far beyond a 300 ms budget
    let mut s = Solver::new(&f, cfg(300)).unwrap();
    let t = std::time::Instant::now();
    let (st, allocs) = solve_counting(&mut s);
    assert_eq!(st, Status::Unknown);
    assert_eq!(allocs, 0);
    assert!(t.elapsed().as_millis() < 1_000, "timeout overshoot: {:?}", t.elapsed());
    assert!(s.best_unsat >= 1);
    assert_eq!(violated(&f, |v| s.best_value(v)), s.best_unsat as usize);
}

#[test]
fn memory_budget_is_enforced_before_allocation() {
    let f = random_ksat(50_000, 200_000, 3, 7);
    match Solver::new(&f, Config { memory_budget: 4 << 20, ..Config::default() }) {
        Err(LoadError::OverBudget { need, budget }) => assert!(need > budget),
        _ => panic!("expected OverBudget"),
    }
    // a moderate budget shrinks the learnt arena instead of failing
    let big = Solver::new(&f, Config { memory_budget: 1 << 30, ..Config::default() }).unwrap();
    let small = Solver::new(&f, Config { memory_budget: 64 << 20, ..Config::default() }).unwrap();
    assert!(small.layout.learnt_lits < big.layout.learnt_lits);
    assert!(small.allocated_bytes <= 64 << 20);
}

#[test]
fn edge_cases() {
    // no clauses
    let f = Formula::new(5);
    let mut s = Solver::new(&f, cfg(1000)).unwrap();
    assert_eq!(s.solve(), Status::Sat);
    // zero variables, zero clauses
    let f = Formula::new(0);
    let mut s = Solver::new(&f, cfg(1000)).unwrap();
    assert_eq!(s.solve(), Status::Sat);
    // empty clause
    let mut f = Formula::new(2);
    f.add_clause(&[]);
    let mut s = Solver::new(&f, cfg(1000)).unwrap();
    assert_eq!(s.solve(), Status::Unsat);
    // contradictory units
    let mut f = Formula::new(1);
    f.add_clause(&[1]);
    f.add_clause(&[-1]);
    let mut s = Solver::new(&f, cfg(1000)).unwrap();
    assert_eq!(s.solve(), Status::Unsat);
    // tautologies only
    let mut f = Formula::new(3);
    f.add_clause(&[1, -1, 2]);
    let mut s = Solver::new(&f, cfg(1000)).unwrap();
    assert_eq!(s.solve(), Status::Sat);
    assert_eq!(f.tautologies_dropped, 1);
    // single variable
    let mut f = Formula::new(1);
    f.add_clause(&[-1]);
    let mut s = Solver::new(&f, cfg(1000)).unwrap();
    assert_eq!(s.solve(), Status::Sat);
    assert!(!s.model_value(0));
}

#[test]
fn dimacs_parsing() {
    let text = "c comment\np cnf 3 2\n1 -2 0\n2 3\n-1 0\n%\n0\n";
    let f = Formula::parse_dimacs(text).unwrap();
    assert_eq!(f.num_vars, 3);
    assert_eq!(f.num_clauses(), 2);
    assert_eq!(f.clause(1).len(), 3);
    assert!(Formula::parse_dimacs("p cnf x 1\n").is_err());
}

#[test]
fn solver_is_reusable_only_via_fresh_workspace_but_deterministic() {
    let f = random_ksat(60, 255, 3, 5);
    let a = { let mut s = Solver::new(&f, cfg(5000)).unwrap(); s.solve() };
    let b = { let mut s = Solver::new(&f, cfg(5000)).unwrap(); s.solve() };
    assert_eq!(a, b);
}

/// Release-only: `check_watches` makes debug builds far too slow to time.
#[test]
#[cfg_attr(debug_assertions, ignore)]
fn deadline_respected_on_mid_instance() {
    let f = random_ksat(300_000, 1_200_000, 3, 7); // ratio 4.0
    for ms in [50u64, 1000] {
        let mut s = Solver::new(&f, Config { timeout_ms: ms, memory_budget: 512 << 20, ..Config::default() }).unwrap();
        let t = std::time::Instant::now();
        let (st, allocs) = solve_counting(&mut s);
        let el = t.elapsed().as_millis() as u64;
        assert_eq!(allocs, 0);
        assert!(el <= ms + 100, "timeout {ms} ms: solve() took {el} ms");
        if st == Status::Sat {
            assert_eq!(violated(&f, |v| s.model_value(v)), 0);
        }
    }
}

#[test]
fn unknown_reports_best_honestly() {
    let f = random_ksat(100_000, 400_000, 3, 9);
    for ms in [1u64, 2, 5] {
        let mut s = Solver::new(&f, Config { timeout_ms: ms, memory_budget: 256 << 20, ..Config::default() }).unwrap();
        let (st, allocs) = solve_counting(&mut s);
        assert_eq!(allocs, 0);
        if st != Status::Unknown {
            continue;
        }
        if s.has_best() {
            assert_eq!(violated(&f, |v| s.best_value(v)), s.best_unsat as usize, "timeout {ms} ms");
        } else {
            assert_eq!(s.best_unsat, u32::MAX, "timeout {ms} ms");
        }
    }
}
