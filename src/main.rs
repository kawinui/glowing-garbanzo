//! Verification & benchmark harness.
//!
//! * A counting global allocator is *armed* around every `solve()` call and
//!   the harness fails loudly if a single allocation happens inside it.
//! * Every SAT model is re-checked here, independently of the solver, against
//!   the raw input clauses.
//! * `--selftest` cross-checks SAT/UNSAT against brute force on thousands of
//!   tiny random formulas.
//!
//! Usage:
//!   zsat <file.cnf> [--timeout MS] [--mem MiB] [--seed N] [--model] [--log] [--no-learning] [--no-relax] [--steepest]
//!   zsat --bench [--timeout MS]
//!   zsat --selftest [COUNT]
//!   zsat --deadline-check

use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering::Relaxed};
use std::time::Instant;
use zsat::controller::NUM_STATES;
use zsat::types::NUM_ACTIONS;
use zsat::*;

// ---------------------------------------------------------------------------
// Counting allocator
// ---------------------------------------------------------------------------

struct Counting;
static ARMED: AtomicBool = AtomicBool::new(false);
static ARMED_ALLOCS: AtomicU64 = AtomicU64::new(0);
static LIVE: AtomicUsize = AtomicUsize::new(0);
static PEAK: AtomicUsize = AtomicUsize::new(0);

unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, l: Layout) -> *mut u8 {
        if ARMED.load(Relaxed) {
            ARMED_ALLOCS.fetch_add(1, Relaxed);
        }
        let now = LIVE.fetch_add(l.size(), Relaxed) + l.size();
        PEAK.fetch_max(now, Relaxed);
        System.alloc(l)
    }
    unsafe fn alloc_zeroed(&self, l: Layout) -> *mut u8 {
        if ARMED.load(Relaxed) {
            ARMED_ALLOCS.fetch_add(1, Relaxed);
        }
        let now = LIVE.fetch_add(l.size(), Relaxed) + l.size();
        PEAK.fetch_max(now, Relaxed);
        System.alloc_zeroed(l)
    }
    unsafe fn dealloc(&self, p: *mut u8, l: Layout) {
        LIVE.fetch_sub(l.size(), Relaxed);
        System.dealloc(p, l)
    }
    unsafe fn realloc(&self, p: *mut u8, l: Layout, n: usize) -> *mut u8 {
        if ARMED.load(Relaxed) {
            ARMED_ALLOCS.fetch_add(1, Relaxed);
        }
        let now = LIVE.fetch_add(n, Relaxed) + n;
        LIVE.fetch_sub(l.size(), Relaxed);
        PEAK.fetch_max(now, Relaxed);
        System.realloc(p, l, n)
    }
}

#[global_allocator]
static GLOBAL: Counting = Counting;

// ---------------------------------------------------------------------------
// Instance generators (load time)
// ---------------------------------------------------------------------------

struct Gen(u64);
impl Gen {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

fn random_ksat(n: u32, m: u32, k: u32, seed: u64) -> Formula {
    let mut g = Gen(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1);
    let mut f = Formula::new(n);
    let mut c = Vec::with_capacity(k as usize);
    for _ in 0..m {
        c.clear();
        while c.len() < k as usize {
            let v = g.below(n as u64) as i32 + 1;
            if c.iter().any(|&x: &i32| x.abs() == v) {
                continue;
            }
            c.push(if g.next() & 1 == 0 { v } else { -v });
        }
        f.add_clause(&c);
    }
    f
}

/// Random 3-SAT filtered to be satisfied by a hidden assignment (guaranteed SAT).
fn planted_3sat(n: u32, m: u32, seed: u64) -> Formula {
    let mut g = Gen(seed.wrapping_mul(0xD1B5_4A32_D192_ED03) | 1);
    let hidden: Vec<bool> = (0..n).map(|_| g.next() & 1 == 1).collect();
    let mut f = Formula::new(n);
    let mut made = 0;
    let mut c = Vec::with_capacity(3);
    while made < m {
        c.clear();
        while c.len() < 3 {
            let v = g.below(n as u64) as i32 + 1;
            if c.iter().any(|&x: &i32| x.abs() == v) {
                continue;
            }
            c.push(if g.next() & 1 == 0 { v } else { -v });
        }
        if c.iter().any(|&d| hidden[(d.unsigned_abs() - 1) as usize] == (d > 0)) {
            f.add_clause(&c);
            made += 1;
        }
    }
    f
}

/// Pigeonhole PHP(p, h): UNSAT iff p > h. Exponential for resolution.
fn pigeonhole(p: u32, h: u32) -> Formula {
    let var = |i: u32, j: u32| (i * h + j + 1) as i32;
    let mut f = Formula::new(p * h);
    for i in 0..p {
        let c: Vec<i32> = (0..h).map(|j| var(i, j)).collect();
        f.add_clause(&c);
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

// ---------------------------------------------------------------------------
// Independent checks
// ---------------------------------------------------------------------------

fn count_violated(f: &Formula, value: impl Fn(u32) -> bool) -> usize {
    (0..f.num_clauses())
        .filter(|&i| !f.clause(i).iter().any(|l| value(l.var()) != l.is_neg()))
        .count()
}

fn brute_force_sat(f: &Formula) -> bool {
    let n = f.num_vars;
    assert!(n <= 20);
    (0u32..(1 << n)).any(|a| count_violated(f, |v| (a >> v) & 1 == 1) == 0)
}

/// Independent reference: plain recursive DPLL with unit propagation
/// (harness-only code, shares nothing with the solver).
fn dpll_sat(f: &Formula) -> bool {
    fn go(cls: &[Vec<Lit>], a: &mut Vec<i8>) -> bool {
        // unit propagation to fixpoint
        let mut trail = Vec::new();
        loop {
            let mut unit = None;
            for c in cls {
                let mut sat = false;
                let mut free = None;
                let mut nfree = 0;
                for &l in c {
                    let v = a[l.var() as usize];
                    if v == 0 {
                        nfree += 1;
                        free = Some(l);
                    } else if (v == 1) != l.is_neg() {
                        sat = true;
                        break;
                    }
                }
                if sat {
                    continue;
                }
                if nfree == 0 {
                    for v in trail {
                        a[v] = 0;
                    }
                    return false;
                }
                if nfree == 1 {
                    unit = free;
                    break;
                }
            }
            match unit {
                Some(l) => {
                    a[l.var() as usize] = if l.is_neg() { -1 } else { 1 };
                    trail.push(l.var() as usize);
                }
                None => break,
            }
        }
        // branch on a variable of the first open clause
        let mut pick = None;
        for c in cls {
            if c.iter().any(|&l| { let v = a[l.var() as usize]; v != 0 && (v == 1) != l.is_neg() }) {
                continue;
            }
            pick = c.iter().find(|l| a[l.var() as usize] == 0).copied();
            break;
        }
        let ok = match pick {
            None => true,
            Some(l) => {
                let v = l.var() as usize;
                a[v] = if l.is_neg() { -1 } else { 1 };
                if go(cls, a) {
                    true
                } else {
                    a[v] = -a[v];
                    let r = go(cls, a);
                    if !r {
                        a[v] = 0;
                    }
                    r
                }
            }
        };
        if !ok {
            for v in trail {
                a[v] = 0;
            }
        }
        ok
    }
    let cls: Vec<Vec<Lit>> = (0..f.num_clauses()).map(|i| f.clause(i).to_vec()).collect();
    let mut a = vec![0i8; f.num_vars as usize];
    go(&cls, &mut a)
}

// ---------------------------------------------------------------------------
// Running
// ---------------------------------------------------------------------------

struct RunReport {
    status: Status,
    ms: f64,
    allocs: u64,
    model_ok: Option<bool>,
    best_unsat: u32,
    /// False when UNKNOWN came back before any assignment was evaluated.
    has_best: bool,
}

fn run(name: &str, f: &Formula, cfg: Config, verbose: bool, print_log: bool, print_model: bool) -> RunReport {
    let t_load = Instant::now();
    let mut s = match Solver::new(f, cfg) {
        Ok(s) => s,
        Err(e) => {
            println!("c [{name}] LOAD REFUSED: {e}");
            return RunReport { status: Status::Unknown, ms: 0.0, allocs: 0, model_ok: None, best_unsat: u32::MAX, has_best: false };
        }
    };
    let load_ms = t_load.elapsed().as_secs_f64() * 1e3;

    ARMED_ALLOCS.store(0, Relaxed);
    ARMED.store(true, Relaxed);
    let t = Instant::now();
    let status = s.solve();
    let ms = t.elapsed().as_secs_f64() * 1e3;
    ARMED.store(false, Relaxed);
    let allocs = ARMED_ALLOCS.load(Relaxed);

    let model_ok = match status {
        Status::Sat => Some(count_violated(f, |v| s.model_value(v)) == 0),
        _ => None,
    };
    if verbose {
        println!("c ------------------------------------------------------------");
        println!(
            "c [{name}] vars={} clauses={} lits={}  workspace={:.2} MiB (budget {:.0} MiB, learnt arena {} lits)  load={load_ms:.1}ms",
            f.num_vars,
            f.num_clauses(),
            f.lits.len(),
            s.allocated_bytes as f64 / 1048576.0,
            cfg.memory_budget as f64 / 1048576.0,
            s.layout.learnt_lits
        );
        let st = &s.stats;
        println!(
            "c   epochs={} conflicts={} decisions={} props={} flips={} probes={} failed={} learnt_units={} reductions={} subsumed={} pure={}",
            st.epochs, st.conflicts, st.decisions, st.propagations, st.sls_flips, st.probes,
            st.failed_lits, st.learnt_units, st.reductions, st.subsumed, st.pure
        );
        print!("c   transitions:");
        for e in s.mode_log.iter() {
            if let EventKind::Mode { from, to, why } = e.kind {
                print!(" [{:.1}ms e{} {}→{} {:?}]", e.t_us as f64 / 1e3, e.epoch, from.name(), to.name(), why);
            }
        }
        println!();
        println!("c   learned Q-weights (state = mode × {{improving, stalling}}):");
        print!("c   {:>22}", "");
        for a in Action::ALL {
            print!("{:>18}", a.name());
        }
        println!();
        for st_i in 0..NUM_STATES {
            let mode = [Mode::Aggressive, Mode::Balanced, Mode::Conservative][st_i / 2];
            print!("c   {:>13}/{:<8}", mode.name(), if st_i % 2 == 0 { "improve" } else { "stall" });
            for a in 0..NUM_ACTIONS {
                let i = st_i * NUM_ACTIONS + a;
                if s.q.n[i] == 0 {
                    print!("{:>18}", "·");
                } else {
                    print!("{:>12.3} ({:>3})", s.q.q[i], s.q.n[i]);
                }
            }
            println!();
        }
        if print_log {
            println!("c   event log ({} dropped):", s.log.dropped);
            for e in s.log.iter() {
                println!("c     {:>9.2}ms e{:<5} {:?}", e.t_us as f64 / 1e3, e.epoch, e.kind);
            }
        }
    }
    let verdict = match status {
        Status::Sat => "SATISFIABLE",
        Status::Unsat => "UNSATISFIABLE",
        Status::Unknown => "UNKNOWN",
    };
    println!(
        "s {verdict:<14} [{name}] {ms:>9.1} ms  allocs-in-solve={allocs}{}{}",
        match model_ok {
            Some(true) => "  model=VERIFIED".to_string(),
            Some(false) => "  model=INVALID!".to_string(),
            None => String::new(),
        },
        match (status, s.has_best()) {
            (Status::Unknown, true) => format!("  best-so-far violates {} clauses", s.best_unsat),
            (Status::Unknown, false) => "  no assignment evaluated within budget".to_string(),
            _ => String::new(),
        }
    );
    if print_model && status == Status::Unknown && !s.has_best() {
        println!("c no best-so-far assignment");
    } else if print_model && status != Status::Unsat {
        let get = |v| if status == Status::Sat { s.model_value(v) } else { s.best_value(v) };
        let mut line = String::from("v");
        for v in 0..f.num_vars {
            let d = v as i64 + 1;
            line += &format!(" {}", if get(v) { d } else { -d });
            if line.len() > 76 {
                println!("{line}");
                line = String::from("v");
            }
        }
        println!("{line} 0");
    }
    RunReport { status, ms, allocs, model_ok, best_unsat: s.best_unsat, has_best: s.has_best() }
}

fn check_one(f: &Formula, truth: bool, seed: u64, tag: &str, base: Config) -> (Status, bool) {
    let cfg = Config { timeout_ms: 5_000, memory_budget: 16 << 20, seed, ..base };
    let mut s = Solver::new(f, cfg).expect("load");
    ARMED_ALLOCS.store(0, Relaxed);
    ARMED.store(true, Relaxed);
    let st = s.solve();
    ARMED.store(false, Relaxed);
    let allocs = ARMED_ALLOCS.load(Relaxed);
    let ok = match st {
        Status::Sat => truth && count_violated(f, |v| s.model_value(v)) == 0,
        Status::Unsat => !truth,
        Status::Unknown => false,
    } && allocs == 0;
    if !ok {
        println!("c   MISMATCH {tag}: vars={} clauses={} solver={st:?} truth_sat={truth} allocs={allocs}", f.num_vars, f.num_clauses());
    }
    (st, ok)
}

fn selftest(count: u32, base: Config) -> bool {
    let mut g = Gen(0xC0FFEE);
    let (mut sat, mut unsat, mut bad) = (0, 0, 0);
    println!("c selftest A: {count} random formulas vs brute force (3–14 vars, ratio 2–7, k=2..4)");
    for i in 0..count {
        let n = 3 + g.below(12) as u32;
        let k = 2 + g.below(3) as u32;
        let m = (n as f64 * (2.0 + g.below(50) as f64 / 10.0)) as u32;
        let f = random_ksat(n, m.max(1), k.min(n), g.next());
        let (st, ok) = check_one(&f, brute_force_sat(&f), g.next(), &format!("A#{i}"), base);
        sat += (st == Status::Sat) as u32;
        unsat += (st == Status::Unsat) as u32;
        bad += (!ok) as u32;
    }
    let nb = (count / 10).max(20);
    println!("c selftest B: {nb} random 3-SAT formulas near the threshold vs reference DPLL (30–60 vars)");
    for i in 0..nb {
        let n = 30 + g.below(31) as u32;
        let m = (n as f64 * (3.8 + g.below(10) as f64 / 10.0)) as u32;
        let f = random_ksat(n, m, 3, g.next());
        let (st, ok) = check_one(&f, dpll_sat(&f), g.next(), &format!("B#{i}"), base);
        sat += (st == Status::Sat) as u32;
        unsat += (st == Status::Unsat) as u32;
        bad += (!ok) as u32;
    }
    println!("c selftest: sat={sat} unsat={unsat} failures={bad}");
    bad == 0
}

fn bench(timeout_ms: u64) -> bool {
    let cfg = Config { timeout_ms, ..Config::default() };
    let suite: Vec<(String, Formula, Option<bool>)> = vec![
        ("uf150-r4.26 #1".into(), random_ksat(150, 639, 3, 11), None),
        ("uf150-r4.26 #2".into(), random_ksat(150, 639, 3, 12), None),
        ("uf250-r4.20".into(), random_ksat(250, 1050, 3, 21), None),
        ("planted-5k-r4.2".into(), planted_3sat(5_000, 21_000, 3), Some(true)),
        ("planted-50k-r4.0".into(), planted_3sat(50_000, 200_000, 4), Some(true)),
        ("random-100k-r3.9".into(), random_ksat(100_000, 390_000, 3, 5), None),
        ("unsat-uf120-r5.5".into(), random_ksat(120, 660, 3, 6), None),
        ("unsat-uf200-r6.0".into(), random_ksat(200, 1200, 3, 7), None),
        ("php-8-7".into(), pigeonhole(8, 7), Some(false)),
        ("php-9-8".into(), pigeonhole(9, 8), Some(false)),
        ("php-8-8 (sat)".into(), pigeonhole(8, 8), Some(true)),
    ];
    let mut ok = true;
    let mut rows = Vec::new();
    for (name, f, expect) in &suite {
        let r = run(name, f, cfg, true, false, false);
        let consistent = match (r.status, expect) {
            (Status::Sat, Some(false)) | (Status::Unsat, Some(true)) => false,
            _ => r.model_ok != Some(false),
        };
        ok &= consistent && r.allocs == 0;
        rows.push((name.clone(), r, consistent));
    }
    println!("c ============================ summary ============================");
    println!("c {:<20} {:>14} {:>10} {:>8} {:>10}", "instance", "result", "ms", "allocs", "best-unsat");
    for (name, r, c) in &rows {
        println!(
            "c {:<20} {:>14} {:>10.1} {:>8} {:>10}{}",
            name,
            format!("{:?}", r.status),
            r.ms,
            r.allocs,
            if r.status == Status::Unknown && r.has_best { r.best_unsat.to_string() } else { "-".into() },
            if *c { "" } else { "   <-- WRONG" }
        );
    }
    println!("c peak process heap: {:.1} MiB", PEAK.load(Relaxed) as f64 / 1048576.0);
    ok
}

/// Release-build check that `solve()` returns within `timeout + bounded overshoot`
/// on a mid-size and a very large instance, and that UNKNOWN reports honestly.
fn deadline_check() -> bool {
    let cases: Vec<(&str, Formula, usize)> = vec![
        ("mid-300k-r4.0", random_ksat(300_000, 1_200_000, 3, 31), 512 << 20),
        ("big-2M-8M", random_ksat(2_000_000, 8_000_000, 3, 32), 2048 << 20),
    ];
    let mut ok = true;
    println!("c {:<14} {:>8} {:>9} {:>12} {:>9} {:>9} {:>9} {:>6}", "instance", "timeout", "solve_ms", "overshoot_ms", "limit_ms", "status", "has_best", "allocs");
    for (name, f, mem) in &cases {
        let (rebuild_ms, eval_ms) = {
            let cfg = Config { timeout_ms: 1, memory_budget: *mem, ..Config::default() };
            Solver::new(f, cfg).expect("load").diag_costs()
        };
        println!("c {name}: one rebuild = {rebuild_ms:.1} ms, one full eval = {eval_ms:.1} ms (overshoot bound = rebuild + eval + 20 ms)");
        for t in [50u64, 100, 1000] {
            let cfg = Config { timeout_ms: t, memory_budget: *mem, ..Config::default() };
            let mut s = Solver::new(f, cfg).expect("load");
            ARMED_ALLOCS.store(0, Relaxed);
            ARMED.store(true, Relaxed);
            let t0 = Instant::now();
            let status = s.solve();
            let ms = t0.elapsed().as_secs_f64() * 1e3;
            ARMED.store(false, Relaxed);
            let allocs = ARMED_ALLOCS.load(Relaxed);
            // acceptance: the only unstoppable units are one rebuild and one eval
            let limit = t as f64 + rebuild_ms + eval_ms + 20.0;
            let mut pass = ms <= limit && allocs == 0;
            if status == Status::Unknown && s.has_best() {
                pass &= count_violated(f, |v| s.best_value(v)) == s.best_unsat as usize;
            }
            if status == Status::Sat {
                pass &= count_violated(f, |v| s.model_value(v)) == 0;
            }
            ok &= pass;
            println!(
                "c {:<14} {:>8} {:>9.1} {:>12.1} {:>9.0} {:>9} {:>9} {:>6}{}",
                name, t, ms, ms - t as f64, limit, format!("{status:?}"), s.has_best(), allocs,
                if pass { "" } else { "   <-- FAIL" }
            );
        }
    }
    ok
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mut cfg = Config::default();
    let (mut file, mut do_bench, mut do_self, mut self_n) = (None, false, false, 3000u32);
    let mut do_deadline = false;
    let (mut model, mut log) = (false, false);
    let mut i = 0;
    while i < args.len() {
        let a = args[i].as_str();
        let num = |i: &mut usize| -> u64 {
            *i += 1;
            args.get(*i).and_then(|s| s.parse().ok()).unwrap_or_else(|| {
                eprintln!("missing/invalid number after {a}");
                std::process::exit(2)
            })
        };
        match a {
            "--timeout" => cfg.timeout_ms = num(&mut i),
            "--mem" => cfg.memory_budget = (num(&mut i) as usize) << 20,
            "--seed" => cfg.seed = num(&mut i),
            "--model" => model = true,
            "--log" => log = true,
            "--no-learning" => cfg.learning = false,
            "--no-relax" => cfg.relaxation = false,
            "--steepest" => cfg.sls_rule = types::SlsRule::Steepest,
            "--bench" => do_bench = true,
            "--deadline-check" => do_deadline = true,
            "--selftest" => {
                do_self = true;
                if let Some(n) = args.get(i + 1).and_then(|s| s.parse().ok()) {
                    self_n = n;
                    i += 1;
                }
            }
            "-h" | "--help" => {
                println!("usage: zsat <file.cnf> [--timeout MS] [--mem MiB] [--seed N] [--model] [--log] [--no-learning] [--no-relax] [--steepest]\n       zsat --bench [--timeout MS]\n       zsat --selftest [COUNT]\n       zsat --deadline-check");
                return;
            }
            _ => file = Some(a.to_string()),
        }
        i += 1;
    }
    let mut ok = true;
    if do_self {
        ok &= selftest(self_n, cfg);
    }
    if do_bench {
        ok &= bench(cfg.timeout_ms);
    }
    if do_deadline {
        ok &= deadline_check();
    }
    if let Some(path) = file {
        let text = std::fs::read_to_string(&path).unwrap_or_else(|e| {
            eprintln!("cannot read {path}: {e}");
            std::process::exit(2)
        });
        let f = Formula::parse_dimacs(&text).unwrap_or_else(|e| {
            eprintln!("parse error: {e}");
            std::process::exit(2)
        });
        let r = run(&path, &f, cfg, true, log, model);
        if r.allocs != 0 || r.model_ok == Some(false) || !ok {
            eprintln!("HARNESS FAILURE");
            std::process::exit(1);
        }
        std::process::exit(match r.status {
            Status::Sat => 10,
            Status::Unsat => 20,
            Status::Unknown => 0,
        });
    }
    if !do_self && !do_bench && !do_deadline {
        println!("nothing to do; try --selftest or --bench (see --help)");
    }
    if !ok {
        eprintln!("HARNESS FAILURE");
        std::process::exit(1);
    }
}
