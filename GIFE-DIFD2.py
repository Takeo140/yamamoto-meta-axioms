# General Information Field Engine + UHA Core + Takeo Evolution + DIFD
# License: Apache 2.0
# Author: Takeo Yamamoto

from dataclasses import dataclass
from typing import Callable, List, Optional

U64_MOD = 2 ** 64


def U64(x: int) -> int:
    """U64: 2^64 有限環として扱う整数ラッパ."""
    return x % U64_MOD


# ─────────────────────────────────────────────
# UHA Core
# ─────────────────────────────────────────────

@dataclass
class UHA:
    """UltraCore HyperAlgebra の n 次元キャリア（Python版）"""
    coords: List[int]  # 各要素は U64 として扱う

    @property
    def n(self) -> int:
        return len(self.coords)

    @staticmethod
    def zero(n: int) -> "UHA":
        return UHA([U64(0)] * n)

    @staticmethod
    def add(x: "UHA", y: "UHA") -> "UHA":
        assert x.n == y.n
        return UHA([U64(a + b) for a, b in zip(x.coords, y.coords)])

    @staticmethod
    def smul(a: int, x: "UHA") -> "UHA":
        a = U64(a)
        return UHA([U64(a * c) for c in x.coords])

    @staticmethod
    def mul_with(c: Callable[[int, int], "UHA"], x: "UHA", y: "UHA") -> "UHA":
        """
        多元代数の乗法（構造定数 c を外部から与える）
        c(j, k): UHA
        """
        n = x.n
        result = [U64(0)] * n
        for i in range(n):
            s = 0
            for j in range(n):
                for k in range(n):
                    cjki = c(j, k).coords[i]
                    s += x.coords[j] * y.coords[k] * cjki
            result[i] = U64(s)
        return UHA(result)

    @staticmethod
    def norm(x: "UHA") -> int:
        """ノルム（量子状態の離散版）"""
        s = 0
        for c in x.coords:
            s += c * c
        return U64(s)


# ─────────────────────────────────────────────
# GIFE Structures
# ─────────────────────────────────────────────

@dataclass
class Entity:
    id: int
    state: UHA
    energy: int  # U64
    mood: int    # U64
    genome: int  # U64


@dataclass
class Topology:
    conn: Callable[[Entity, Entity], int]  # U64
    viscosity: int                         # U64
    curvature: int                         # U64


@dataclass
class FieldState:
    entities: List[Entity]
    entropy: int      # U64
    topology: Topology


@dataclass
class Dynamics:
    update_entity: Callable[[Entity, int], Entity]
    update_entropy: Callable[[FieldState, int], int]
    update_topology: Callable[[Topology, List[Entity]], Topology]


@dataclass
class Evolution:
    mutate: Callable[[Entity], Entity]
    select: Callable[[List[Entity]], List[Entity]]
    adapt: Callable[[Entity, int], Entity]


@dataclass
class EvolutionCore:
    fitness: Callable[[Entity, FieldState], int]  # U64
    diversity: List[Entity]


# ─────────────────────────────────────────────
# DIFD: 離散流体力学
# ─────────────────────────────────────────────

def diffuse(top: Topology, e: Entity, neighbors: List[Entity]) -> UHA:
    """離散拡散：隣接 Entity の UHA 状態を平均化する"""
    n = e.state.n
    total = UHA.zero(n)
    norm_sum = 0

    for nb in neighbors:
        w = U64(top.conn(e, nb))
        total = UHA.add(total, UHA.smul(w, nb.state))
        norm_sum += w

    norm_sum = U64(norm_sum)
    if norm_sum == 0:
        return e.state
    # mod 2^64 の逆元（0 の場合は上で弾いている）
    inv = pow(norm_sum, -1, U64_MOD)
    return UHA.smul(inv, total)


def vortex(top: Topology, e: Entity) -> UHA:
    """離散渦度：Topology.curvature を使って UHA を回転させる"""
    c = U64(top.curvature)
    return UHA.smul(c, e.state)


def pressure(entropy: int, e: Entity) -> UHA:
    """離散圧力：entropy を圧力として UHA を押し出す"""
    ent = U64(entropy)
    return UHA.smul(ent, e.state)


def fluid_update(top: Topology, entropy: int, e: Entity, neighbors: List[Entity]) -> UHA:
    """離散流体力学の総合更新則"""
    d = diffuse(top, e, neighbors)
    v = vortex(top, e)
    p = pressure(entropy, e)
    return UHA.add(UHA.add(d, v), p)


def update_entity_fluid(
    dyn: Dynamics,
    top: Topology,
    entropy: int,
    neighbors: List[Entity],
    e: Entity,
) -> Entity:
    """Entity 更新に流体力学を統合した完成版"""
    new_state = fluid_update(top, entropy, e, neighbors)
    base = dyn.update_entity(e, entropy)
    return Entity(
        id=base.id,
        state=new_state,
        energy=base.energy,
        mood=base.mood,
        genome=base.genome,
    )


# ─────────────────────────────────────────────
# Takeo Evolution
# ─────────────────────────────────────────────

def env_changed(prev: FieldState, curr: FieldState) -> bool:
    return (
        prev.entropy != curr.entropy
        or prev.topology.viscosity != curr.topology.viscosity
        or prev.topology.curvature != curr.topology.curvature
    )


def argmax_entity(core: EvolutionCore, env: FieldState) -> Entity:
    if not core.diversity:
        n = env.entities[0].state.n if env.entities else 1
        return Entity(
            id=0,
            state=UHA.zero(n),
            energy=U64(0),
            mood=U64(0),
            genome=U64(0),
        )

    best = core.diversity[0]
    best_score = core.fitness(best, env)
    for cand in core.diversity[1:]:
        score = core.fitness(cand, env)
        if score > best_score:
            best = cand
            best_score = score
    return best


@dataclass
class Engine:
    dynamics: Dynamics
    evolution: Evolution
    takeo_core: Optional[EvolutionCore] = None


def step_classic(eng: Engine, s: FieldState) -> FieldState:
    updated = [
        update_entity_fluid(eng.dynamics, s.topology, s.entropy, s.entities, e)
        for e in s.entities
    ]

    adapted = [eng.evolution.adapt(e, s.entropy) for e in updated]
    selected = eng.evolution.select(adapted)
    mutated = [eng.evolution.mutate(e) for e in selected]

    new_topology = eng.dynamics.update_topology(s.topology, mutated)
    new_entropy = eng.dynamics.update_entropy(
        FieldState(entities=mutated, entropy=s.entropy, topology=new_topology),
        s.entropy,
    )

    return FieldState(entities=mutated, entropy=new_entropy, topology=new_topology)


def step_takeo(
    eng: Engine,
    core: EvolutionCore,
    prev: FieldState,
    curr: FieldState,
) -> FieldState:
    if env_changed(prev, curr):
        best = argmax_entity(core, curr)
        return FieldState(
            entities=[best],
            entropy=curr.entropy,
            topology=curr.topology,
        )
    else:
        return prev


def step(eng: Engine, s: FieldState) -> FieldState:
    if eng.takeo_core is None:
        return step_classic(eng, s)
    next_state = step_classic(eng, s)
    return step_takeo(eng, eng.takeo_core, s, next_state)


# ─────────────────────────────────────────────
# Stream & Evolution Loop
# ─────────────────────────────────────────────

@dataclass
class Stream:
    head: FieldState
    tail: Callable[[], "Stream"]


def evolution_takeo(eng: Engine, core: EvolutionCore, s0: FieldState) -> Stream:
    def corec(prev: FieldState, curr: FieldState) -> Stream:
        next_state = step_takeo(eng, core, prev, curr)
        return Stream(
            head=prev,
            tail=lambda: corec(curr, step_classic(eng, curr)),
        )

    return corec(s0, step_classic(eng, s0))


# ─────────────────────────────────────────────
# 簡易な「実用」向けデフォルト実装例
# ─────────────────────────────────────────────

def default_conn(e1: Entity, e2: Entity) -> int:
    """単純な接続関数：IDの差に基づく重み."""
    return U64(abs(e1.id - e2.id) + 1)


def default_update_entity(e: Entity, entropy: int) -> Entity:
    """エネルギーとムードを少し変化させる簡易モデル."""
    new_energy = U64(e.energy + entropy // 1000)
    new_mood = U64(e.mood + entropy // 2000)
    return Entity(id=e.id, state=e.state, energy=new_energy, mood=new_mood, genome=e.genome)


def default_update_entropy(fs: FieldState, prev_entropy: int) -> int:
    """エントロピーを少し増加させる簡易モデル."""
    return U64(prev_entropy + len(fs.entities))


def default_update_topology(top: Topology, entities: List[Entity]) -> Topology:
    """粘性と曲率を少し変化させる簡易モデル."""
    new_viscosity = U64(top.viscosity + len(entities))
    new_curvature = U64(top.curvature + len(entities) // 2)
    return Topology(conn=top.conn, viscosity=new_viscosity, curvature=new_curvature)


def default_mutate(e: Entity) -> Entity:
    """genome を少し変化させる簡易突然変異."""
    new_genome = U64(e.genome + 1)
    return Entity(id=e.id, state=e.state, energy=e.energy, mood=e.mood, genome=new_genome)


def default_select(entities: List[Entity]) -> List[Entity]:
    """全 Entity をそのまま選択（フィルタなし）。"""
    return entities


def default_adapt(e: Entity, entropy: int) -> Entity:
    """entropy に応じて mood を調整する簡易適応."""
    new_mood = U64(e.mood + entropy // 500)
    return Entity(id=e.id, state=e.state, energy=e.energy, mood=new_mood, genome=e.genome)


def default_fitness(e: Entity, fs: FieldState) -> int:
    """energy と mood を足し合わせた簡易フィットネス."""
    return U64(e.energy + e.mood)


def make_default_engine(n: int, num_entities: int = 4) -> Engine:
    """簡易な初期エンジン構築."""
    # 初期 UHA 状態
    entities: List[Entity] = []
    for i in range(num_entities):
        state = UHA([U64(i + j) for j in range(n)])
        entities.append(
            Entity(
                id=i,
                state=state,
                energy=U64(10 + i),
                mood=U64(5 + i),
                genome=U64(100 + i),
            )
        )

    topo = Topology(conn=default_conn, viscosity=U64(1), curvature=U64(1))
    entropy = U64(10)
    fs0 = FieldState(entities=entities, entropy=entropy, topology=topo)

    dyn = Dynamics(
        update_entity=default_update_entity,
        update_entropy=default_update_entropy,
        update_topology=default_update_topology,
    )

    evo = Evolution(
        mutate=default_mutate,
        select=default_select,
        adapt=default_adapt,
    )

    core = EvolutionCore(
        fitness=default_fitness,
        diversity=entities,
    )

    return Engine(dynamics=dyn, evolution=evo, takeo_core=core), fs0


# 実行例
if __name__ == "__main__":
    eng, s0 = make_default_engine(n=3, num_entities=4)
    s = s0
    for step_idx in range(5):
        print(f"Step {step_idx}: entropy={s.entropy}, num_entities={len(s.entities)}")
        s = step(eng, s)
