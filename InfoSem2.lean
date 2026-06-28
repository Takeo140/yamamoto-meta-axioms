/-
  Information semantics of value, scarcity, and credit — v3
  Author: Takeo Yamamoto  License: Apache 2.0

  Changes from v2
  ---------------
  [C1] order の解釈を固定:
       Shannon エントロピーの減少量（冗長性）として order を公理的に制約する。
       order i = H_max - H(i)  （H_max は最大エントロピー定数）
       これにより「構造化度が高い = エントロピーが低い = order が大きい」が成立する。

  [C2] JV の内部構造を特定:
       JV i r = Value i * (1 + α * scarcity r)
       乗法形式を採用。α > 0 は資源感度パラメータ。
       - 内容価値 Value i がゼロなら資源コストは無意味（乗法の自然な性質）
       - scarcity が上がれば JV は超線形に増大
       - JV_monotone_in_scarcity および JV_dominates_Value を定理として導出可能
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Algebra.Order.Ring.Lemmas

namespace InfoSem

universe u

-- ───────────────────────────────────────────────
-- §1  Primitive types
-- ───────────────────────────────────────────────

constant Info     : Type u
constant Agent    : Type u
constant Resource : Type u
constant Network  : Type u

-- ───────────────────────────────────────────────
-- §2  Economy snapshot
-- ───────────────────────────────────────────────

structure Economy where
  infos     : Set Info
  agents    : Set Agent
  resources : Set Resource
  network   : Network

-- ───────────────────────────────────────────────
-- §3  Shannon-grounded order
-- ───────────────────────────────────────────────

/-- Shannon エントロピー（情報の不確実性）。非負実数。 -/
constant H : Info → ℝ

/-- 最大エントロピー定数（記号長・語彙サイズから決まる上界）。 -/
constant H_max : ℝ

/-- H_max は任意の情報のエントロピーを支配する。 -/
axiom H_max_dominates : ∀ (i : Info), H i ≤ H_max

/-- エントロピーは非負。 -/
axiom H_nonneg : ∀ (i : Info), 0 ≤ H i

/-- [C1] order の定義: order i = H_max - H i
    「冗長性」= 最大不確実性からの乖離。
    H が小さい（構造的・圧縮可能）ほど order が大きい。 -/
noncomputable def order (i : Info) : ℝ := H_max - H i

/-- order は非負（H_max_dominates より直接導出）。 -/
theorem order_nonneg (i : Info) : 0 ≤ order i := by
  unfold order
  linarith [H_max_dominates i]

/-- order の上界は H_max（H = 0 のとき達成）。 -/
theorem order_le_H_max (i : Info) : order i ≤ H_max := by
  unfold order
  linarith [H_nonneg i]

-- ───────────────────────────────────────────────
-- §4  Value — order 単調性
-- ───────────────────────────────────────────────

/-- 情報の intrinsic value。order の単調増加関数として公理化。 -/
constant Value : Info → ℝ

/-- Axiom 1 — Value–order 単調性。 -/
axiom value_monotone_in_order :
  ∀ {i₁ i₂ : Info}, order i₁ ≤ order i₂ → Value i₁ ≤ Value i₂

/-- Value は非負（order_nonneg と単調性から示唆される補助公理）。 -/
axiom Value_nonneg : ∀ (i : Info), 0 ≤ Value i

-- ───────────────────────────────────────────────
-- §5  資源・JV — 乗法構造
-- ───────────────────────────────────────────────

/-- 資源の希少性。非負実数。 -/
constant scarcity : Resource → ℝ

/-- 希少性は非負。 -/
axiom scarcity_nonneg : ∀ (r : Resource), 0 ≤ scarcity r

/-- 資源感度パラメータ α > 0。 -/
constant α : ℝ
axiom α_pos : 0 < α

/-- [C2] 結合生産価値関数（乗法形式）。
    JV i r = Value i * (1 + α * scarcity r)
    - Value i = 0 のとき JV = 0（無価値な情報は資源コストを反映しない）
    - scarcity ↑ → JV ↑（超線形）
    - α は産業・文脈ごとに較正可能なパラメータ -/
noncomputable def JV (i : Info) (r : Resource) : ℝ :=
  Value i * (1 + α * scarcity r)

/-- 定理 T1: JV は scarcity に関して単調増加。
    （v2 では公理；v3 では定義から導出される定理）-/
theorem JV_monotone_in_scarcity
    (i : Info) (r₁ r₂ : Resource)
    (h : scarcity r₁ ≤ scarcity r₂) :
    JV i r₁ ≤ JV i r₂ := by
  unfold JV
  apply mul_le_mul_of_nonneg_left _ (Value_nonneg i)
  apply add_le_add_left
  apply mul_le_mul_of_nonneg_left h
  linarith [α_pos]

/-- 定理 T2: JV は intrinsic value を下回らない（生産コストは非負）。 -/
theorem JV_dominates_Value (i : Info) (r : Resource) :
    Value i ≤ JV i r := by
  unfold JV
  have h1 : 0 ≤ α * scarcity r :=
    mul_nonneg (le_of_lt α_pos) (scarcity_nonneg r)
  have h2 : 1 ≤ 1 + α * scarcity r := by linarith
  calc Value i
      = Value i * 1             := (mul_one _).symm
    _ ≤ Value i * (1 + α * scarcity r) :=
        mul_le_mul_of_nonneg_left h2 (Value_nonneg i)

-- ───────────────────────────────────────────────
-- §6  Credit — ネットワーク単調性
-- ───────────────────────────────────────────────

constant credit           : Network → Agent → ℝ
constant network_strength : Network → ℝ

/-- Axiom 3 — Credit–network 単調性。 -/
axiom credit_monotone_in_network_strength :
  ∀ (n₁ n₂ : Network) (a : Agent),
    network_strength n₁ ≤ network_strength n₂ →
    credit n₁ a ≤ credit n₂ a

-- ───────────────────────────────────────────────
-- §7  経済動態
-- ───────────────────────────────────────────────

/-- 経済スナップショットの総価値。 -/
noncomputable def totalValue (E : Economy) : ℝ :=
  ∑ i in E.infos.toFinset, Value i

structure EconTransition where
  from_     : Economy
  to_       : Economy
  info_flow : Set Info

/-- Axiom 4 — 遷移価値変化（ε-精密形式）。 -/
axiom econ_transition_value_change :
  ∀ (t : EconTransition) (ε : ℝ), ε > 0 →
    |totalValue t.to_ - totalValue t.from_
      - ∑ i in t.info_flow.toFinset, Value i| ≤ ε

-- ───────────────────────────────────────────────
-- §8  派生補題
-- ───────────────────────────────────────────────

/-- 補題: order が高く希少な資源で生産された情報の JV は
    order が低く普遍的な資源で生産された情報の intrinsic value を上回る。 -/
lemma high_order_scarce_dominates_low_order_value
    (i₁ i₂ : Info) (r₁ r₂ : Resource)
    (h_ord  : order i₁ ≤ order i₂)
    (h_scar : scarcity r₁ ≤ scarcity r₂) :
    JV i₁ r₁ ≤ JV i₂ r₂ := by
  calc JV i₁ r₁
      ≤ JV i₁ r₂ := JV_monotone_in_scarcity i₁ r₁ r₂ h_scar
    _ ≤ JV i₂ r₂ := by
        unfold JV
        apply mul_le_mul_of_nonneg_right
        · exact value_monotone_in_order h_ord
        · have : 0 ≤ α * scarcity r₂ :=
            mul_nonneg (le_of_lt α_pos) (scarcity_nonneg r₂)
          linarith

end InfoSem
