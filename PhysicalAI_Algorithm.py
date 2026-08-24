"""
Physical AI Algorithm — derived from ACM-TY (Abstract Computation Model)
Original formal model: Lean 4, ZMod(2^64) algebra, by Takeo Yamamoto.
License: Apache 2.0 (matching the source Lean module).

This file re-embodies the ACM-TY subsystems as a real-time, physically
realizable multi-agent (swarm robotics) control algorithm. Nothing here
is a "translation by renaming" — each subsystem keeps its original role,
moved from a discrete algebraic domain onto a continuous physical one.

Mapping table
-------------
UHA (n)          -> continuous per-agent state vector: [x, y, vx, vy]
BSCM             -> fixed-point / integer control law, safe for embedded
                     real-time loops (the same discrete-step logic that
                     made BSCM analyzable in Lean makes it deterministic
                     and WCET-bounded on a microcontroller)
Topology         -> inter-agent sensing/communication graph (who can see whom)
GIFE.FieldState  -> the swarm: all agents + shared entropy + topology
DIFD.diffuse     -> distributed consensus / formation-keeping update
DIFD.vortex      -> circulation term for obstacle skirting
DIFD.pressure    -> repulsion term for collision avoidance, scaled by
                     the entropy (disturbance) estimate: more disturbance
                     -> more defensive spacing
DIFD.cfl         -> a stability/safety envelope check: an update is only
                     applied if it stays inside a bounded-velocity regime;
                     otherwise the agent fails safe and holds its state
Evolution        -> ONLINE, EVENT-TRIGGERED gain adaptation. Exactly like
                     stepTakeo vs stepClassic in the Lean model: control
                     gains are re-optimized only when the environment
                     changes materially (entropy/viscosity/curvature
                     jump), not every tick. This is the physically
                     important design choice carried over verbatim: it
                     keeps the algorithm cheap enough to run on real,
                     power/compute-constrained hardware.

Run this file directly for a demo: 8 agents converge on a circular
formation, a disturbance is injected mid-run, and the evolutionary layer
re-adapts control gains only at that moment.
"""

from __future__ import annotations
import numpy as np
from dataclasses import dataclass, field
from typing import Callable

STATE_DIM = 4  # [x, y, vx, vy]
U16_MASK = 0xFFFF  # stand-in for the ZMod(2^64) discrete channel, sized for demo speed


# ─────────────────────────────────────────────
# 1. UHA -> continuous agent state
# ─────────────────────────────────────────────

def uha_add(x: np.ndarray, y: np.ndarray) -> np.ndarray:
    return x + y


def uha_smul(a: float, x: np.ndarray) -> np.ndarray:
    return a * x


def uha_norm(x: np.ndarray) -> float:
    return float(np.dot(x, x))


# ─────────────────────────────────────────────
# 2. BSCM -> discrete/fixed-point control core
# ─────────────────────────────────────────────

def bscm_delta(s: int) -> int:
    """Deterministic halving step (parity-governed) — used here as a
    lightweight, embedded-safe damping ratchet on the quantized control word."""
    s &= U16_MASK
    return (s // 2) if (s % 2 == 0) else ((s + 1) // 2)


def bscm_control_step(current_state: int, external_input: int) -> int:
    return bscm_delta((current_state + external_input) & U16_MASK)


def bscm_entropy(s: int) -> int:
    """Fast disturbance estimate from the low bytes of the quantized state
    (analogous to reading vibration/noise off an IMU's low-order bits)."""
    s &= U16_MASK
    b0 = s & 0xFF
    b1 = (s >> 8) & 0xFF
    return b0 + b1


# ─────────────────────────────────────────────
# 3 & 4. GIFE / DIFD -> swarm field + distributed fluid-style control
# ─────────────────────────────────────────────

@dataclass
class Entity:
    id: int
    state: np.ndarray            # [x, y, vx, vy]
    energy: float                # battery / actuation budget
    mood: float                  # confidence / uncertainty scalar
    genome: np.ndarray           # control gains [Kp, Kd]
    discrete: int                # quantized control word (BSCM channel)


@dataclass
class Topology:
    sensing_radius: float
    viscosity: float             # damping bound
    curvature: float             # obstacle-circulation strength

    def conn(self, a: Entity, b: Entity) -> float:
        if a.id == b.id:
            return 0.0
        d = np.linalg.norm(a.state[:2] - b.state[:2])
        if d > self.sensing_radius or d < 1e-6:
            return 0.0
        return 1.0 / d  # closer neighbors weigh more, matches connMatrix intent


@dataclass
class FieldState:
    entities: list[Entity]
    entropy: float
    topology: Topology


def clip_viscosity(v: float, cap: float = 5.0) -> float:
    return min(v, cap)


def normalize_pressure(p: float, cap: float = 50.0) -> float:
    return min(p, cap)


def decay_vortex(curvature: float) -> float:
    return curvature / 2


DT = 0.1


def diffuse(top: Topology, e: Entity, neighbors: list[Entity], target: np.ndarray) -> np.ndarray:
    """Formation-keeping consensus accel: weighted pull toward neighbors'
    positions, plus a Kp/Kd pull toward this agent's assigned target
    (Kp, Kd are the evolved genome — this is where Evolution's output
    actually re-enters the physical loop)."""
    total = np.zeros(2)
    wsum = 0.0
    for nb in neighbors:
        w = top.conn(e, nb)
        total += w * nb.state[:2]
        wsum += w
    consensus_pull = (total / wsum - e.state[:2]) if wsum > 0 else np.zeros(2)

    kp, kd = e.genome
    target_pull = kp * (target[:2] - e.state[:2]) - kd * e.state[2:]
    accel = 0.4 * consensus_pull + target_pull
    return np.array([0.0, 0.0, accel[0], accel[1]])  # acceleration lives in the velocity slots


def vortex(top: Topology, e: Entity) -> np.ndarray:
    """Circulation accel: rotates a fraction of current velocity to skirt
    obstacles instead of colliding head-on."""
    c = decay_vortex(top.curvature)
    vx, vy = e.state[2], e.state[3]
    return np.array([0.0, 0.0, -vy, vx]) * c


def pressure(entropy: float, e: Entity, neighbors: list[Entity]) -> np.ndarray:
    """Collision-avoidance accel: repel from any neighbor closer than a
    safety margin, scaled by the disturbance estimate (noisier
    environment -> more defensive spacing)."""
    p = normalize_pressure(entropy) / 50.0  # normalized to [0, 1]
    margin = 0.8
    accel = np.zeros(2)
    for nb in neighbors:
        delta = e.state[:2] - nb.state[:2]
        dist = np.linalg.norm(delta) + 1e-6
        if dist < margin:
            accel += (delta / dist) * (margin - dist) * (1.0 + p)
    return np.array([0.0, 0.0, accel[0], accel[1]])


def cfl_ok(accel: np.ndarray, visc: float) -> bool:
    """Safety envelope: reject accelerations too large for the damping
    bound to absorb in one tick. Fails safe (hold velocity) otherwise."""
    return uha_norm(accel) < visc * visc * 25


def fluid_update(top: Topology, entropy: float, e: Entity,
                  neighbors: list[Entity], target: np.ndarray) -> np.ndarray:
    visc = clip_viscosity(top.viscosity)
    d = diffuse(top, e, neighbors, target)
    v = vortex(top, e)
    p = pressure(entropy, e, neighbors)
    accel = uha_add(uha_add(d, v), p)
    if not cfl_ok(accel, visc):
        accel = np.zeros(STATE_DIM)  # fail-safe: coast, don't lurch
    new_vel = e.state[2:] + DT * accel[2:]
    new_vel = np.clip(new_vel, -4.0, 4.0)
    new_pos = e.state[:2] + DT * new_vel
    return np.concatenate([new_pos, new_vel])


# ─────────────────────────────────────────────
# 5. Evolution -> event-triggered online gain adaptation
# ─────────────────────────────────────────────

def env_changed(prev: FieldState, curr: FieldState, tol: float = 120.0) -> bool:
    return (abs(prev.entropy - curr.entropy) > tol
            or prev.topology.viscosity != curr.topology.viscosity
            or prev.topology.curvature != curr.topology.curvature)


def fitness(gains: np.ndarray, e: Entity, target: np.ndarray) -> float:
    """One-step lookahead: simulate what these candidate gains would do
    to tracking error, then penalize excess actuation effort. Must depend
    on the candidate, or selection degenerates to minimizing effort alone."""
    kp, kd = gains
    accel = kp * (target[:2] - e.state[:2]) - kd * e.state[2:]
    predicted_vel = np.clip(e.state[2:] + DT * accel, -4.0, 4.0)
    predicted_pos = e.state[:2] + DT * predicted_vel
    err = np.linalg.norm(predicted_pos - target[:2])
    effort = np.linalg.norm(gains)
    return -(err + 0.02 * effort)


def evolve_gains(e: Entity, target: np.ndarray, rng: np.random.Generator,
                  pop_size: int = 6) -> np.ndarray:
    """Small (mu, lambda)-style evolutionary strategy: perturb current
    gains, keep the fittest candidate. Mirrors mutate/select/adapt."""
    candidates = [e.genome + rng.normal(0, 0.15, size=2) for _ in range(pop_size)]
    candidates = [np.clip(c, 0.05, 3.0) for c in candidates]
    scored = [(fitness(c, e, target), c) for c in candidates]
    scored.sort(key=lambda t: t[0], reverse=True)
    return scored[0][1]


# ─────────────────────────────────────────────
# 6. Engine.step -> one physical control tick
# ─────────────────────────────────────────────

def step(field_state: FieldState, targets: dict[int, np.ndarray],
          rng: np.random.Generator, prev_field_state: FieldState | None = None) -> FieldState:
    entities = field_state.entities
    top = field_state.topology

    # DIFD-driven physical update per agent
    new_entities = []
    for e in entities:
        neighbors = [o for o in entities if o.id != e.id]
        target = targets[e.id]
        new_state = fluid_update(top, field_state.entropy, e, neighbors, target)

        # BSCM discrete control channel (deterministic, embedded-safe)
        err_word = int(min(abs(new_state[0] - target[0]) * 100, U16_MASK))
        new_discrete = bscm_control_step(e.discrete, err_word)
        local_entropy = bscm_entropy(new_discrete)

        new_entities.append(Entity(
            id=e.id, state=new_state,
            energy=max(0.0, e.energy - 0.01 * np.linalg.norm(new_state[2:])),
            mood=local_entropy / 255.0,
            genome=e.genome, discrete=new_discrete,
        ))

    new_field_entropy = float(np.mean([e.mood * 255 for e in new_entities]))
    new_field = FieldState(entities=new_entities, entropy=new_field_entropy, topology=top)

    # Evolution layer: only re-adapt gains on a real environment change (stepTakeo pattern)
    if prev_field_state is not None and env_changed(prev_field_state, new_field):
        adapted = []
        for e in new_field.entities:
            new_gains = evolve_gains(e, targets[e.id], rng)
            adapted.append(Entity(e.id, e.state, e.energy, e.mood, new_gains, e.discrete))
        new_field = FieldState(entities=adapted, entropy=new_field.entropy, topology=top)

    return new_field


# ─────────────────────────────────────────────
# 7. Demo: swarm converges on a circular formation, disturbance mid-run
# ─────────────────────────────────────────────

def run_demo():
    rng = np.random.default_rng(42)
    n_agents = 8
    radius = 3.0
    targets = {}
    entities = []
    for i in range(n_agents):
        angle = 2 * np.pi * i / n_agents
        targets[i] = np.array([radius * np.cos(angle), radius * np.sin(angle), 0.0, 0.0])
        start = rng.normal(0, 1.5, size=2)
        entities.append(Entity(
            id=i, state=np.array([start[0], start[1], 0.0, 0.0]),
            energy=100.0, mood=0.0, genome=np.array([0.5, 0.2]), discrete=0,
        ))

    topology = Topology(sensing_radius=6.0, viscosity=1.0, curvature=0.2)
    field_state = FieldState(entities=entities, entropy=0.0, topology=topology)

    trajectories = {i: [entities[i].state[:2].copy()] for i in range(n_agents)}
    adaptation_events = []

    T = 200
    prev = None
    for t in range(T):
        if t == 100:
            # Inject a disturbance: raise curvature/viscosity as if an
            # obstacle field just appeared.
            topology = Topology(sensing_radius=6.0, viscosity=1.0, curvature=1.5)
            field_state = FieldState(field_state.entities, field_state.entropy, topology)

        new_field = step(field_state, targets, rng, prev_field_state=prev)
        if prev is not None and env_changed(prev, new_field):
            adaptation_events.append(t)
        prev = field_state
        field_state = new_field
        for e in field_state.entities:
            trajectories[e.id].append(e.state[:2].copy())

    final_err = np.mean([
        np.linalg.norm(e.state[:2] - targets[e.id][:2]) for e in field_state.entities
    ])
    print(f"final mean formation error: {final_err:.4f}")
    print(f"gain-adaptation events triggered at ticks: {adaptation_events}")

    try:
        import matplotlib.pyplot as plt
        fig, ax = plt.subplots(figsize=(6, 6))
        for i, pts in trajectories.items():
            pts = np.array(pts)
            ax.plot(pts[:, 0], pts[:, 1], alpha=0.6, lw=1)
            ax.scatter(*pts[-1], s=30)
            ax.scatter(*targets[i][:2], marker='x', c='black', s=40)
        ax.set_title("ACM-TY-derived swarm control: trajectories to target formation")
        ax.set_aspect('equal')
        fig.tight_layout()
        fig.savefig("/home/claude/swarm_trajectories.png", dpi=150)
        print("saved plot to swarm_trajectories.png")
    except ImportError:
        pass


if __name__ == "__main__":
    run_demo()
