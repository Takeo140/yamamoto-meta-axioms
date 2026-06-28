/-
  Information semantics of value, scarcity, and credit
  Author: Takeo Yamamoto License Apache 2.0
  Note: This is a *foundational* axiomatization, not an implementation.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic

namespace InfoSem

/-- 基本的な対象：情報・主体・資源・ネットワーク -/
universe u

/-- 情報の型（抽象） -/
constant Info : Type u

/-- 主体（エージェント） -/
constant Agent : Type u

/-- 計算資源（GPU時間・電力などを抽象化） -/
constant Resource : Type u

/-- ネットワーク（主体間の接続構造） -/
constant Network : Type u

/-- 経済状態（世界の情報・資源・ネットワークのスナップショット） -/
structure Economy where
  infos    : Set Info
  agents   : Set Agent
  resources : Set Resource
  network  : Network

/-- 価値を実数で測る抽象的評価関数 -/
constant Value : Info → ℝ

/-- 計算資源の「希少性」を測る関数 -/
constant scarcity : Resource → ℝ

/-- ネットワーク上の主体の「信用」を測る関数 -/
constant credit : Network → Agent → ℝ

/-- 情報の「秩序度」（圧縮可能性・構造化度などの抽象指標） -/
constant order : Info → ℝ

/-- 情報の秩序と価値の意味論的対応：価値は秩序の単調関数である -/
axiom value_monotone_in_order :
  ∀ {i₁ i₂ : Info}, order i₁ ≤ order i₂ → Value i₁ ≤ Value i₂

/-- 計算資源の希少性と価値の対応：
    同じ情報でも、より希少な資源を要する生成は価値を押し上げる（抽象的公理）。 -/
axiom value_respects_scarcity :
  ∀ (i : Info) (r₁ r₂ : Resource),
    scarcity r₁ ≤ scarcity r₂ →
    Value i + scarcity r₁ ≤ Value i + scarcity r₂

/-- ネットワーク効果としての信用：
    ネットワークの「強度」が上がれば、主体の信用も単調に増加する。 -/
constant network_strength : Network → ℝ

axiom credit_monotone_in_network_strength :
  ∀ (n₁ n₂ : Network) (a : Agent),
    network_strength n₁ ≤ network_strength n₂ →
    credit n₁ a ≤ credit n₂ a

/-- 経済とは「情報の流れ」であることの抽象化：
    経済状態間の遷移は、情報集合の変化として表現される。 -/
structure EconTransition where
  from to : Economy
  info_flow : Set Info
  -- info_flow は from.infos から to.infos への「移動・生成・消滅」を抽象的に表す

/-- 情報の流れが価値の総量を変化させる：  
    経済遷移における価値総量の変化は、info_flow 上の Value の総和で近似される。 -/
def totalValue (E : Economy) : ℝ :=
  ∑ i in E.infos.toFinset, Value i

axiom econ_transition_value_change :
  ∀ (t : EconTransition),
    totalValue t.to - totalValue t.from
      ≈ ∑ i in t.info_flow.toFinset, Value i
  -- 「≈」はここでは概念的近似を表す記号として使用（実装時は適切な関係に置換）

/- ここまでで：

   ・価値＝情報の秩序（order と Value の単調対応）
   ・希少性＝計算資源（scarcity）
   ・信用＝ネットワーク効果（network_strength と credit の単調対応）
   ・経済＝情報の流れ（EconTransition と totalValue）

   を Lean 上の公理的枠組みとして定義した。
-/

end InfoSem
