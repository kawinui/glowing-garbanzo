use zsat::*;
fn main() {
    let n: u32 = std::env::args().nth(1).and_then(|s| s.parse().ok()).unwrap_or(100_000);
    let r: f64 = std::env::args().nth(2).and_then(|s| s.parse().ok()).unwrap_or(3.9);
    let mut x = 88172645463325252u64;
    let mut f = Formula::new(n);
    for _ in 0..(n as f64 * r) as u32 {
        let mut c = [0i32; 3];
        let mut i = 0;
        while i < 3 {
            x ^= x << 13; x ^= x >> 7; x ^= x << 17;
            let v = (x % n as u64) as i32 + 1;
            if c[..i].iter().any(|y| y.abs() == v) { continue; }
            c[i] = if (x >> 40) & 1 == 0 { v } else { -v };
            i += 1;
        }
        f.add_clause(&c);
    }
    let mut s = Solver::new(&f, Config::default()).unwrap();
    let t = std::time::Instant::now();
    let (b, fl) = s.diag_sls(3000);
    let secs = t.elapsed().as_secs_f64();
    println!("best={b} flips={fl} {:.2} Mflips/s", fl as f64 / secs / 1e6);
}
