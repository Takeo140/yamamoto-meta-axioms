"""
Physical AI Algorithm — BATCHED / vectorized variant of physical_ai_acm.py

The previous version was semantically correct but implemented UHA's linear
algebra by looping over Entity objects in Python — which throws away
exactly the property that makes UHA fast: it's a vector space, and
Topology.connMatrix is a *linear operator* on it. This version represents
the whole swarm as a single (n, k) state matrix and expresses every DIFD
term as a matrix operation, so it runs through BLAS instead of the
Python interpreter:

  diffuse (consensus)  -> W @ pos          (W = normalized connectivity matrix)
  vortex               -> elementwise rotate of the (n,2) velocity block
  pressure             -> pairwise (n,n,2) delta tensor, masked + summed
  BSCM channel         -> uint32 numpy array ops instead of a Python int per agent
  Evolution            -> (pop_size, n, 2) candidate tensor, argmax over axis 0

Same physics, same event-triggered stepTakeo/stepClassic split — only the
implementation strategy changes, from "loop of scalars" to "one matrix
per tick".
"""

from __future__ import annotations
import time
import numpy as np
from dataclasses import dataclass

DT = 0.1
U16_MASK = np.uint32(0xFFFF)


@dataclass
class TopologyParams:
    sensing_radius: float
    viscosity: float
    curvature: float


@dataclass
class SwarmState:
    pos: np.ndarray       # (n, 2)
    vel: np.ndarray       # (n, 2)
    genome: np.ndarray    # (n, 2) -> Kp, Kd per agent
    discrete: np.ndarray  # (n,) uint32 — BSCM channel
    entropy: float
    top: TopologyParams


def conn_matrix(pos: np.ndarray, top: TopologyParams) -> np.ndarray:
    """Vectorized Topology.conn: pairwise 1/distance, masked by sensing
    radius, zero diagonal. This IS connMatrix — computed once per tick as
    a dense (n, n) linear operator instead of n^2 scalar Python calls."""
    diff = pos[:, None, :] - pos[None, :, :]           # (n, n, 2)
    dist = np.linalg.norm(diff, axis=-1)                # (n, n)
    np.fill_diagonal(dist, np.inf)
    w = np.where(dist <= top.sensing_radius, 1.0 / np.maximum(dist, 1e-6), 0.0)
    return w  # (n, n)


def diffuse_batch(pos, vel, genome, targets, W) -> np.ndarray:
    """Consensus + target-pull acceleration for every agent at once."""
    wsum = W.sum(axis=1, keepdims=True)                # (n, 1)
    neighbor_avg = np.divide(W @ pos, wsum, out=np.zeros_like(pos), where=wsum > 0)
    consensus_pull = np.where(wsum > 0, neighbor_avg - pos, 0.0)
    kp = genome[:, 0:1]
    kd = genome[:, 1:2]
    target_pull = kp * (targets - pos) - kd * vel
    return 0.4 * consensus_pull + target_pull            # (n, 2) acceleration


def vortex_batch(vel, curvature: float) -> np.ndarray:
    c = curvature / 2
    return np.stack([-vel[:, 1], vel[:, 0]], axis=1) * c


def pressure_batch(pos, entropy: float, margin: float = 0.8) -> np.ndarray:
    p = min(entropy, 50.0) / 50.0
    diff = pos[:, None, :] - pos[None, :, :]            # (n, n, 2)
    dist = np.linalg.norm(diff, axis=-1)                 # (n, n)
    np.fill_diagonal(dist, np.inf)
    close = dist < margin
    mag = np.where(close, (margin - dist) * (1.0 + p), 0.0)  # (n, n)
    unit = np.divide(diff, dist[..., None], out=np.zeros_like(diff), where=dist[..., None] < np.inf)
    return (unit * mag[..., None]).sum(axis=1)            # (n, 2)


def bscm_step_batch(discrete: np.ndarray, err_word: np.ndarray) -> np.ndarray:
    s = (discrete + err_word) & U16_MASK
    even = (s % 2 == 0)
    return np.where(even, s // 2, (s + 1) // 2).astype(np.uint32)


def bscm_entropy_batch(s: np.ndarray) -> np.ndarray:
    b0 = s & np.uint32(0xFF)
    b1 = (s >> np.uint32(8)) & np.uint32(0xFF)
    return (b0 + b1).astype(np.float64)


def env_changed(prev_entropy, curr_entropy, prev_top, curr_top, tol=120.0) -> bool:
    return (abs(prev_entropy - curr_entropy) > tol
            or prev_top.viscosity != curr_top.viscosity
            or prev_top.curvature != curr_top.curvature)


def evolve_gains_batch(pos, vel, genome, targets, rng, pop_size: int = 6) -> np.ndarray:
    """Vectorized (mu, lambda)-ES: perturb every agent's gains pop_size
    times AT ONCE as a (pop_size, n, 2) tensor, score all candidates with
    a one-step lookahead, argmax per agent along the population axis."""
    n = pos.shape[0]
    noise = rng.normal(0, 0.15, size=(pop_size, n, 2))
    candidates = np.clip(genome[None, :, :] + noise, 0.05, 3.0)   # (pop, n, 2)
    kp = candidates[:, :, 0]
    kd = candidates[:, :, 1]
    accel = kp[:, :, None] * (targets[None] - pos[None]) - kd[:, :, None] * vel[None]
    pred_vel = np.clip(vel[None] + DT * accel, -4.0, 4.0)
    pred_pos = pos[None] + DT * pred_vel
    err = np.linalg.norm(pred_pos - targets[None], axis=-1)        # (pop, n)
    effort = np.linalg.norm(candidates, axis=-1)                   # (pop, n)
    score = -(err + 0.02 * effort)                                  # (pop, n)
    best = np.argmax(score, axis=0)                                 # (n,)
    return candidates[best, np.arange(n), :]


def step_batch(s: SwarmState, targets: np.ndarray, rng: np.random.Generator,
               prev_entropy: float | None = None, prev_top: TopologyParams | None = None) -> SwarmState:
    visc = min(s.top.viscosity, 5.0)
    W = conn_matrix(s.pos, s.top)
    d = diffuse_batch(s.pos, s.vel, s.genome, targets, W)
    v = vortex_batch(s.vel, s.top.curvature)
    p = pressure_batch(s.pos, s.entropy)
    accel = d + v + p                                     # (n, 2)

    unsafe = (np.sum(accel * accel, axis=1) >= visc * visc * 25)
    accel = np.where(unsafe[:, None], 0.0, accel)          # fail-safe per agent

    new_vel = np.clip(s.vel + DT * accel, -4.0, 4.0)
    new_pos = s.pos + DT * new_vel

    err_word = np.minimum(np.abs(new_pos[:, 0] - targets[:, 0]) * 100, float(U16_MASK)).astype(np.uint32)
    new_discrete = bscm_step_batch(s.discrete, err_word)
    local_entropy = bscm_entropy_batch(new_discrete)
    new_entropy = float(local_entropy.mean())

    new_genome = s.genome
    if prev_entropy is not None and env_changed(prev_entropy, new_entropy, prev_top, s.top):
        new_genome = evolve_gains_batch(new_pos, new_vel, s.genome, targets, rng)

    return SwarmState(pos=new_pos, vel=new_vel, genome=new_genome,
                       discrete=new_discrete, entropy=new_entropy, top=s.top)


# ─────────────────────────────────────────────
# Benchmark: batched vs. the original per-entity loop version
# ─────────────────────────────────────────────

def bench_batch(n_agents: int, T: int = 500) -> float:
    rng = np.random.default_rng(1)
    angles = 2 * np.pi * np.arange(n_agents) / n_agents
    targets = np.stack([3.0 * np.cos(angles), 3.0 * np.sin(angles)], axis=1)
    pos = rng.normal(0, 1.5, size=(n_agents, 2))
    vel = np.zeros((n_agents, 2))
    genome = np.tile(np.array([0.5, 0.2]), (n_agents, 1))
    discrete = np.zeros(n_agents, dtype=np.uint32)
    top = TopologyParams(sensing_radius=6.0, viscosity=1.0, curvature=0.2)
    s = SwarmState(pos, vel, genome, discrete, entropy=0.0, top=top)

    prev_entropy, prev_top = None, None
    t0 = time.perf_counter()
    for _ in range(T):
        ns = step_batch(s, targets, rng, prev_entropy, prev_top)
        prev_entropy, prev_top = s.entropy, s.top
        s = ns
    t1 = time.perf_counter()
    return (t1 - t0) / T


if __name__ == "__main__":
    print("batched (matrix) implementation:")
    for n in [8, 20, 50, 100, 500, 1000]:
        dt = bench_batch(n)
        print(f"  n_agents={n:5d}  {dt*1000:8.4f} ms/tick  ({1/dt:9.0f} ticks/sec)")
