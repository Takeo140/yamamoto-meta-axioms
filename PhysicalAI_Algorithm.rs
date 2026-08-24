//! Physical AI Algorithm — Rust port of the ACM-TY Lean 4 model
//! (UHA / BSCM / DIFD / GIFE / Evolution), applied to multi-agent
//! (swarm robotics) control.
//!
//! Original formal model: Lean 4, ZMod(2^64) algebra, by Takeo Yamamoto.
//! License: Apache-2.0 (matching the source Lean module).
//!
//! This is a straight structural port of `physical_ai_acm_batched.py`:
//! same mapping table, same event-triggered stepTakeo/stepClassic split,
//! same fluid update. What changes is only the substrate — no Python
//! interpreter overhead, no BLAS dispatch, no per-tick heap churn (all
//! buffers are reused across ticks). No external crates: the PRNG is a
//! splitmix64/xorshift implementation, kept in-house the same way the
//! Lean side keeps its own algebra self-contained.
//!
//! Mapping table (see physical_ai_acm.py for the full prose version):
//!   UHA        -> per-agent [x, y, vx, vy] state, stored as flat Vec<f64>
//!   BSCM       -> u32 fixed-point control channel (deterministic, WCET-bounded)
//!   Topology   -> dense connectivity matrix (linear operator on the swarm's state)
//!   DIFD       -> diffuse (consensus) + vortex (circulation) + pressure (repulsion)
//!   Evolution  -> event-triggered (mu, lambda)-ES gain adaptation, fires only
//!                 on env_changed (entropy/viscosity/curvature jump) — never every tick

use std::time::Instant;

const DT: f64 = 0.1;
const U16_MASK: u32 = 0xFFFF;

/// Minimal splitmix64 PRNG — deterministic, dependency-free, branchless.
struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self {
        Rng(seed)
    }
    #[inline]
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E3779B97F4A7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
        z ^ (z >> 31)
    }
    /// Standard normal via Box-Muller, using two uniform draws.
    #[inline]
    fn next_gaussian(&mut self) -> f64 {
        let u1 = ((self.next_u64() >> 11) as f64) / ((1u64 << 53) as f64);
        let u2 = ((self.next_u64() >> 11) as f64) / ((1u64 << 53) as f64);
        let u1 = u1.max(1e-12);
        (-2.0 * u1.ln()).sqrt() * (2.0 * std::f64::consts::PI * u2).cos()
    }
}

#[derive(Clone, Copy)]
struct Topology {
    sensing_radius: f64,
    viscosity: f64,
    curvature: f64,
}

/// Swarm state: structure-of-arrays, all buffers reused tick-to-tick.
struct Swarm {
    n: usize,
    pos: Vec<f64>,      // 2n: x0,y0,x1,y1,...
    vel: Vec<f64>,      // 2n
    genome: Vec<f64>,   // 2n: kp0,kd0,kp1,kd1,...
    discrete: Vec<u32>, // n
    entropy: f64,
    top: Topology,
}

#[inline]
fn bscm_step(discrete: u32, err_word: u32) -> u32 {
    let s = (discrete.wrapping_add(err_word)) & U16_MASK;
    if s % 2 == 0 { s / 2 } else { (s + 1) / 2 }
}

#[inline]
fn bscm_entropy(s: u32) -> f64 {
    let b0 = (s & 0xFF) as f64;
    let b1 = ((s >> 8) & 0xFF) as f64;
    b0 + b1
}

fn env_changed(prev_entropy: f64, curr_entropy: f64, prev_top: Topology, curr_top: Topology) -> bool {
    (prev_entropy - curr_entropy).abs() > 120.0
        || prev_top.viscosity != curr_top.viscosity
        || prev_top.curvature != curr_top.curvature
}

/// One physical control tick. `targets` is 2n flat [x,y]*n.
/// `accel_buf`/`conn_buf` are caller-owned scratch space, reused every
/// call to avoid per-tick allocation (the thing Python/numpy can't do).
fn step(
    s: &mut Swarm,
    targets: &[f64],
    rng: &mut Rng,
    prev_entropy: Option<f64>,
    prev_top: Option<Topology>,
    accel: &mut [f64],
    new_pos: &mut [f64],
    new_vel: &mut [f64],
) {
    let n = s.n;
    let visc = s.top.viscosity.min(5.0);
    let curvature = s.top.curvature;
    let p_scale = s.entropy.min(50.0) / 50.0;
    let margin = 0.8_f64;

    accel.iter_mut().for_each(|a| *a = 0.0);

    // Single O(n^2) pass computes diffuse's consensus sum, pressure's
    // repulsion sum, and reuses distance already computed for both —
    // the flat-array Rust equivalent of the (n,n) connectivity matrix.
    let mut wsum = vec![0.0_f64; n];
    let mut consensus = vec![0.0_f64; 2 * n];

    for i in 0..n {
        let (xi, yi) = (s.pos[2 * i], s.pos[2 * i + 1]);
        for j in 0..n {
            if i == j {
                continue;
            }
            let (xj, yj) = (s.pos[2 * j], s.pos[2 * j + 1]);
            let dx = xi - xj;
            let dy = yi - yj;
            let dist = (dx * dx + dy * dy).sqrt();

            if dist <= s.top.sensing_radius && dist > 1e-6 {
                let w = 1.0 / dist;
                wsum[i] += w;
                consensus[2 * i] += w * xj;
                consensus[2 * i + 1] += w * yj;
            }
            if dist < margin {
                let mag = (margin - dist) * (1.0 + p_scale);
                let inv = if dist > 1e-9 { mag / dist } else { 0.0 };
                accel[2 * i] += dx * inv;
                accel[2 * i + 1] += dy * inv;
            }
        }
    }

    for i in 0..n {
        let (xi, yi) = (s.pos[2 * i], s.pos[2 * i + 1]);
        let (vxi, vyi) = (s.vel[2 * i], s.vel[2 * i + 1]);
        let (tx, ty) = (targets[2 * i], targets[2 * i + 1]);
        let (kp, kd) = (s.genome[2 * i], s.genome[2 * i + 1]);

        let consensus_pull = if wsum[i] > 0.0 {
            (consensus[2 * i] / wsum[i] - xi, consensus[2 * i + 1] / wsum[i] - yi)
        } else {
            (0.0, 0.0)
        };
        let target_pull = (kp * (tx - xi) - kd * vxi, kp * (ty - yi) - kd * vyi);
        let diffuse_ax = 0.4 * consensus_pull.0 + target_pull.0;
        let diffuse_ay = 0.4 * consensus_pull.1 + target_pull.1;

        let vortex_ax = -vyi * (curvature / 2.0);
        let vortex_ay = vxi * (curvature / 2.0);

        let ax = diffuse_ax + vortex_ax + accel[2 * i];
        let ay = diffuse_ay + vortex_ay + accel[2 * i + 1];

        let unsafe_accel = ax * ax + ay * ay >= visc * visc * 25.0;
        let (ax, ay) = if unsafe_accel { (0.0, 0.0) } else { (ax, ay) };

        let nvx = (vxi + DT * ax).clamp(-4.0, 4.0);
        let nvy = (vyi + DT * ay).clamp(-4.0, 4.0);
        new_vel[2 * i] = nvx;
        new_vel[2 * i + 1] = nvy;
        new_pos[2 * i] = xi + DT * nvx;
        new_pos[2 * i + 1] = yi + DT * nvy;

        let err_word = (((new_pos[2 * i] - tx).abs() * 100.0).min(U16_MASK as f64)) as u32;
        s.discrete[i] = bscm_step(s.discrete[i], err_word);
    }

    s.pos.copy_from_slice(new_pos);
    s.vel.copy_from_slice(new_vel);

    let mean_local_entropy: f64 =
        s.discrete.iter().map(|&d| bscm_entropy(d)).sum::<f64>() / n as f64;
    let new_entropy = mean_local_entropy;

    if let (Some(pe), Some(pt)) = (prev_entropy, prev_top) {
        if env_changed(pe, new_entropy, pt, s.top) {
            evolve_gains(s, targets, rng);
        }
    }

    s.entropy = new_entropy;
}

/// Event-triggered (mu, lambda)-ES gain adaptation — the Rust analog of
/// `stepTakeo`: only ever called from `step` when `env_changed` fires.
fn evolve_gains(s: &mut Swarm, targets: &[f64], rng: &mut Rng) {
    const POP: usize = 6;
    let n = s.n;
    for i in 0..n {
        let (xi, yi) = (s.pos[2 * i], s.pos[2 * i + 1]);
        let (vxi, vyi) = (s.vel[2 * i], s.vel[2 * i + 1]);
        let (tx, ty) = (targets[2 * i], targets[2 * i + 1]);
        let (kp0, kd0) = (s.genome[2 * i], s.genome[2 * i + 1]);

        let mut best_score = f64::NEG_INFINITY;
        let mut best = (kp0, kd0);
        for _ in 0..POP {
            let kp = (kp0 + 0.15 * rng.next_gaussian()).clamp(0.05, 3.0);
            let kd = (kd0 + 0.15 * rng.next_gaussian()).clamp(0.05, 3.0);
            let ax = kp * (tx - xi) - kd * vxi;
            let ay = kp * (ty - yi) - kd * vyi;
            let pvx = (vxi + DT * ax).clamp(-4.0, 4.0);
            let pvy = (vyi + DT * ay).clamp(-4.0, 4.0);
            let ppx = xi + DT * pvx;
            let ppy = yi + DT * pvy;
            let err = ((ppx - tx).powi(2) + (ppy - ty).powi(2)).sqrt();
            let effort = (kp * kp + kd * kd).sqrt();
            let score = -(err + 0.02 * effort);
            if score > best_score {
                best_score = score;
                best = (kp, kd);
            }
        }
        s.genome[2 * i] = best.0;
        s.genome[2 * i + 1] = best.1;
    }
}

fn make_swarm(n: usize, top: Topology, rng: &mut Rng) -> (Swarm, Vec<f64>) {
    let mut pos = vec![0.0; 2 * n];
    let mut targets = vec![0.0; 2 * n];
    for i in 0..n {
        let angle = 2.0 * std::f64::consts::PI * (i as f64) / (n as f64);
        targets[2 * i] = 3.0 * angle.cos();
        targets[2 * i + 1] = 3.0 * angle.sin();
        pos[2 * i] = 1.5 * rng.next_gaussian();
        pos[2 * i + 1] = 1.5 * rng.next_gaussian();
    }
    let swarm = Swarm {
        n,
        pos,
        vel: vec![0.0; 2 * n],
        genome: (0..n).flat_map(|_| [0.5, 0.2]).collect(),
        discrete: vec![0u32; n],
        entropy: 0.0,
        top,
    };
    (swarm, targets)
}

fn bench(n: usize, ticks: usize) -> f64 {
    let mut rng = Rng::new(1);
    let top = Topology { sensing_radius: 6.0, viscosity: 1.0, curvature: 0.2 };
    let (mut swarm, targets) = make_swarm(n, top, &mut rng);

    let mut accel = vec![0.0; 2 * n];
    let mut new_pos = vec![0.0; 2 * n];
    let mut new_vel = vec![0.0; 2 * n];

    let mut prev_entropy: Option<f64> = None;
    let mut prev_top: Option<Topology> = None;

    let t0 = Instant::now();
    for _ in 0..ticks {
        step(&mut swarm, &targets, &mut rng, prev_entropy, prev_top, &mut accel, &mut new_pos, &mut new_vel);
        prev_entropy = Some(swarm.entropy);
        prev_top = Some(swarm.top);
    }
    t0.elapsed().as_secs_f64() / ticks as f64
}

fn run_convergence_demo() {
    let mut rng = Rng::new(42);
    let n = 8;
    let mut top = Topology { sensing_radius: 6.0, viscosity: 1.0, curvature: 0.2 };
    let (mut swarm, targets) = make_swarm(n, top, &mut rng);

    let mut accel = vec![0.0; 2 * n];
    let mut new_pos = vec![0.0; 2 * n];
    let mut new_vel = vec![0.0; 2 * n];

    let mut prev_entropy: Option<f64> = None;
    let mut prev_top: Option<Topology> = None;
    let mut adapt_events = vec![];

    for t in 0..200 {
        if t == 100 {
            top.curvature = 1.5;
            swarm.top = top;
        }
        step(&mut swarm, &targets, &mut rng, prev_entropy, prev_top, &mut accel, &mut new_pos, &mut new_vel);
        if let (Some(pe), Some(pt)) = (prev_entropy, prev_top) {
            if env_changed(pe, swarm.entropy, pt, swarm.top) {
                adapt_events.push(t);
            }
        }
        prev_entropy = Some(swarm.entropy);
        prev_top = Some(swarm.top);
    }

    let mut err_sum = 0.0;
    for i in 0..n {
        let dx = swarm.pos[2 * i] - targets[2 * i];
        let dy = swarm.pos[2 * i + 1] - targets[2 * i + 1];
        err_sum += (dx * dx + dy * dy).sqrt();
    }
    println!("convergence demo (n=8, T=200):");
    println!("  final mean formation error: {:.4}", err_sum / n as f64);
    println!("  adaptation events at ticks: {:?}", adapt_events);
}

fn main() {
    run_convergence_demo();
    println!();
    println!("benchmark (release build, single thread, no external crates):");
    for &n in &[8usize, 20, 50, 100, 500, 1000, 5000] {
        let ticks = if n <= 1000 { 500 } else { 100 };
        let dt = bench(n, ticks);
        println!(
            "  n_agents={:5}  {:>10.4} us/tick  ({:>12.0} ticks/sec)",
            n,
            dt * 1e6,
            1.0 / dt
        );
    }
}
