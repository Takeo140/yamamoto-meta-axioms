/-
  UHA Discrete Quantum Computation Kernel (離散型量子計算核)
  Base core: UHA_Core.lean
  License: Apache 2.0
  Author: Takeo Yamamoto
-/
import Mathlib
import UHA_Core

open BigOperators

namespace UHA

variable {n : Nat}

/-! ## 状態：計算基底 -/

/-- 計算基底状態 |i⟩ -/
def basis (i : Fin n) : UHA n :=
  ⟨fun j => if j = i then 1 else 0⟩

theorem norm_basis (i : Fin n) : UHA.norm (basis i) = 1 := by
  unfold UHA.norm basis
  simp

/-! ## ゲート：UOp（ノルム保存）の具体例 -/

/-- 置換ゲート（X, CNOT, SWAP など）：座標の並べ替え。ノルム保存は和の並べ替え不変性から従う -/
def permGate (σ : Equiv.Perm (Fin n)) : UOp n :=
  ⟨fun v => ⟨fun i => v.coords (σ.symm i)⟩, fun v => by
    unfold UHA.norm
    exact Equiv.sum_comp σ.symm (fun i => v.coords i * v.coords i)⟩

/-- 対角ゲート（Z, 離散位相ゲートなど）：各 u i が u i * u i = 1 を満たすとき、ノルム保存 -/
def diagGate (u : Fin n → U64) (hu : ∀ i, u i * u i = 1) : UOp n :=
  ⟨fun v => ⟨fun i => u i * v.coords i⟩, fun v => by
    unfold UHA.norm
    refine Finset.sum_congr rfl fun i _ => ?_
    show (u i * v.coords i) * (u i * v.coords i) = v.coords i * v.coords i
    calc (u i * v.coords i) * (u i * v.coords i)
        = (u i * u i) * (v.coords i * v.coords i) := by ring
      _ = v.coords i * v.coords i := by rw [hu i, one_mul]⟩

/-- Pauli-X（1 量子ビット、次元 2） -/
def gateX : UOp 2 := permGate (Equiv.swap 0 1)

/-- Pauli-Z（1 量子ビット、次元 2） -/
def gateZ : UOp 2 :=
  diagGate ![1, -1] (by intro i; fin_cases i <;> simp)

/-- CNOT（2 量子ビット、次元 4）：|10⟩ と |11⟩ を入れ替える -/
def gateCNOT : UOp 4 := permGate (Equiv.swap 2 3)

/-- SWAP（2 量子ビット、次元 4）：|01⟩ と |10⟩ を入れ替える -/
def gateSWAP : UOp 4 := permGate (Equiv.swap 1 2)

/-! ## 回路：ゲート列の実行とノルム保存 -/

/-- 回路 = ゲート列 -/
abbrev Circuit (n : Nat) := List (UOp n)

/-- 回路の実行（先頭のゲートから順に作用） -/
def runCircuit : Circuit n → UHA n → UHA n
  | [], v => v
  | g :: gs, v => runCircuit gs (g.f v)

/-- 任意の回路はノルムを保存する（基底核の中心定理） -/
theorem runCircuit_norm (c : Circuit n) (v : UHA n) :
    UHA.norm (runCircuit c v) = UHA.norm v := by
  induction c generalizing v with
  | nil => rfl
  | cons g gs ih =>
    simp only [runCircuit]
    rw [ih, g.unitary_like]

/-! ## 複合系：テンソル積 -/

/-- 状態のテンソル積（次元 n * m）。インデックスは Fin n × Fin m と同一視 -/
def kron {m : Nat} (x : UHA n) (y : UHA m) : UHA (n * m) :=
  ⟨fun k =>
    let p := finProdFinEquiv.symm k
    x.coords p.1 * y.coords p.2⟩

end UHA

