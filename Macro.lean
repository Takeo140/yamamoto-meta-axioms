import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Ring.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
  # マクロ経済理論における有効需要と動学的均衡の定式化

  目的:
  ミクロ的インセンティブから導出された総生産が、マクロの「有効需要（購買力）」の
  制約によってどのように決定されるかを数理的に記述する。
  
  モデルのバグ（有効需要の過少による総不況）を防ぎ、
  マクロ経済システムが持続可能な均衡を維持するための条件を完全証明する。
-/

/-- 
  マクロ経済の制度・環境変数
  τ: 税率, G: 再分配（基礎所得）
-/
structure MacroInstitution where
  τ : ℝ
  G : ℝ
  τ_nonneg : 0 ≤ τ
  τ_le_one : τ ≤ 1
  G_nonneg : 0 ≤ G

/-- 
  マクロ経済全体の集計（アグリゲート）変数
  Y_potential: 社会全体の潜在的な総生産量（供給サイドの限界）
  C_aggregate: 社会全体の総消費需要（需要サイドの限界）
-/
structure MacroSystem where
  Y_potential : ℝ
  C_aggregate : ℝ
  Y_pos : 0 < Y_potential
  C_pos : 0 < C_aggregate

namespace MacroEconomics

/-- 
  ケインズ的有効需要の原理 (Principle of Effective Demand):
  実際の経済出力（実際のGDP: Y_actual）は、
  供給能力（Y_potential）と有効需要（C_aggregate）の「小さい方」に制約される。
  
  ここでは、需要がボトルネックとなる「不況均衡（バグ状態）」を
  Y_actual ≤ C_aggregate という不等式制約として定式化。
-/
def isEffectiveDemandEquilibrium (sys : MacroSystem) (Y_actual : ℝ) : Prop :=
  Y_actual ≤ sys.C_aggregate ∧ Y_actual ≤ sys.Y_potential

/-- 
  マクロの所得分配と購買力関数:
  一般層の限界消費傾向（MPC: Marginal Propensity to Consume）を `c` とすると、
  再分配 `G` が増えるほど、社会全体の総消費需要（C_aggregate）は底上げされる。
  ここでは、再分配政策が需要を拡張する動学関係を定義。
-/
def demandFunction (inst : MacroInstitution) (base_demand : ℝ) (c : ℝ) : ℝ :=
  base_demand + c * (2 * inst.G)

/-- 
  【マクロ持続可能性定理】
  適切な再分配（G > 0）によって総消費需要（C_aggregate）が潜在的生産力（Y_potential）
  と同等以上に維持されているならば、実際の総生産（Y_actual）が
  潜在的な生産能力を100%発揮した状態（フル稼働均衡）を達成可能であることを証明する。
-/
theorem exists_full_employment_equilibrium 
    (sys : MacroSystem) 
    (inst : MacroInstitution)
    (base_demand : ℝ)
    (c : ℝ)
    (h_mpc : 0 < c)
    (h_demand_filled : sys.Y_potential ≤ demandFunction inst base_demand c) :
    ∃ (Y_actual : ℝ), 
      Y_actual = sys.Y_potential ∧ 
      (sys.C_aggregate = demandFunction inst base_demand c → isEffectiveDemandEquilibrium sys Y_actual) := by
  -- 実際のGDP（Y_actual）として、潜在生産力（Y_potential）そのものを witness として投入
  use sys.Y_potential
  constructor
  · -- Y_actual = Y_potential は定義より自明
    rfl
  · -- 需要が満たされている条件下で、これが有効需要の均衡条件を満たすことの証明
    intro h_c_eq
    dsimp [isEffectiveDemandEquilibrium]
    constructor
    · -- Y_potential ≤ C_aggregate の証明
      rw [h_c_eq]
      exact h_demand_filled
    · -- Y_potential ≤ Y_potential は反射律より自明
      exact le_refl sys.Y_potential

end MacroEconomics
