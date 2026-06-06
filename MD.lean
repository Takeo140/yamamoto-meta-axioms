import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Ring.Lemmas
import Mathlib.Tactic.Nlinarith
import Mathlib.Tactic.Ring

/-!
  # メカニズムデザインに基づく「最適経済制度」の定式化

  目的:
  個人の利潤・生産インセンティブ（アクセル）を破壊せず、
  かつ格差による市場崩壊（バグ）を防ぐ「最適税制・再分配」の数理構造を定義する。

  ## 証明戦略（sorry除去）
  - witness: τ=0, G=0 の InstitutionalDesign を明示的に構成
  - isFiscalSustainable: 0 * (...) ≥ 2 * 0 は自明
  - 最大性: 財政制約下で W(τ,G) ≤ (1/2)(1-τ²)(Ar²+Ap²) ≤ (1/2)(Ar²+Ap²) = W(0,0)
-/

/--
  社会の環境定義 (Institutional Framework)
  インセンティブと再分配のバランスを管理するパラメータ
-/
structure InstitutionalDesign where
  τ : ℝ  -- 税率 (Tax Rate): 0 ≤ τ < 1
  G : ℝ  -- 保障給付 (Minimum Guaranteed Income / セーフティネット): G ≥ 0
  τ_nonneg : 0 ≤ τ
  τ_lt_one : τ < 1
  G_nonneg : 0 ≤ G

/--
  経済エージェント（個人）の定義
  能力(A)に応じて、手取りが最大になるように自発的に努力量(e)を決定する。
-/
structure Agent where
  ability : ℝ     -- 個人の能力・IQ・技術力 (A > 0)
  ability_pos : 0 < ability

namespace OptimalEconomy

/--
  エージェントの最適化行動（ミクロのリアリズム）
  手取り所得（税引後＋給付）から努力のコストを引いた「自己効用」を最大化する。
-/
def agentUtility (system : InstitutionalDesign) (ag : Agent) (e : ℝ) : ℝ :=
  ((1 - system.τ) * (ag.ability * e) + system.G) - (1 / 2 * e ^ 2)

/--
  最適な努力量の導出 (インセンティブ整合性条件: Incentive Compatibility)
  一階の条件（FOC）より、最適な努力量は e* = (1 - τ) * A となる。
-/
def optimalEffort (system : InstitutionalDesign) (ag : Agent) : ℝ :=
  (1 - system.τ) * ag.ability

/--
  個人の最大生産量（社会への貢献度）
-/
def agentProduction (system : InstitutionalDesign) (ag : Agent) : ℝ :=
  ag.ability * (optimalEffort system ag)

/--
  政府の財政制約（サステナブル条件）
  全員から徴収した税の総和が一律給付の総和以上である必要がある。
  2人モデル（優秀層: rich, 普通層: poor）で定式化。
-/
def isFiscalSustainable (system : InstitutionalDesign) (rich poor : Agent) : Prop :=
  system.τ * (agentProduction system rich + agentProduction system poor) ≥ 2 * system.G

/--
  社会的厚生関数 (Social Welfare Function):
  社会全体の豊かさの評価指標。ここでは全員の効用の総和。

  展開すると: W(τ,G) = (1/2)(1-τ)²(Ar²+Ap²) + 2G
-/
def socialWelfare (system : InstitutionalDesign) (rich poor : Agent) : ℝ :=
  agentUtility system rich (optimalEffort system rich) +
  agentUtility system poor (optimalEffort system poor)

/-! ## 補題群 -/

/-- agentUtility を optimalEffort で評価した閉形式 -/
lemma agentUtility_optimalEffort (sys : InstitutionalDesign) (ag : Agent) :
    agentUtility sys ag (optimalEffort sys ag) =
    (1 / 2) * (1 - sys.τ) ^ 2 * ag.ability ^ 2 + sys.G := by
  simp only [agentUtility, optimalEffort]
  ring

/-- socialWelfare の閉形式 -/
lemma socialWelfare_eq (sys : InstitutionalDesign) (rich poor : Agent) :
    socialWelfare sys rich poor =
    (1 / 2) * (1 - sys.τ) ^ 2 * (rich.ability ^ 2 + poor.ability ^ 2) + 2 * sys.G := by
  simp only [socialWelfare, agentUtility_optimalEffort]
  ring

/-- isFiscalSustainable の閉形式（agentProduction 展開後） -/
lemma fiscalSustainable_eq (sys : InstitutionalDesign) (rich poor : Agent) :
    isFiscalSustainable sys rich poor ↔
    sys.τ * (1 - sys.τ) * (rich.ability ^ 2 + poor.ability ^ 2) ≥ 2 * sys.G := by
  simp only [isFiscalSustainable, agentProduction, optimalEffort]
  constructor <;> intro h <;> nlinarith [h]

/--
  財政制約下での socialWelfare の上界:
  sustainable ならば W(τ,G) ≤ (1/2)(1-τ²)(Ar²+Ap²)
-/
lemma welfare_upper_bound (sys : InstitutionalDesign) (rich poor : Agent)
    (hfs : isFiscalSustainable sys rich poor) :
    socialWelfare sys rich poor ≤
    (1 / 2) * (1 - sys.τ ^ 2) * (rich.ability ^ 2 + poor.ability ^ 2) := by
  rw [socialWelfare_eq]
  rw [fiscalSustainable_eq] at hfs
  nlinarith [sys.τ_nonneg, sys.τ_lt_one, rich.ability_pos, poor.ability_pos,
             sq_nonneg rich.ability, sq_nonneg poor.ability]

/--
  τ=0, G=0 の witness が W = (1/2)(Ar²+Ap²) を達成する
-/
lemma zero_tax_welfare (rich poor : Agent) :
    let sys : InstitutionalDesign :=
      { τ := 0, G := 0, τ_nonneg := le_refl 0,
        τ_lt_one := by norm_num, G_nonneg := le_refl 0 }
    socialWelfare sys rich poor =
    (1 / 2) * (rich.ability ^ 2 + poor.ability ^ 2) := by
  simp [socialWelfare_eq]

/--
  τ=0, G=0 は財政制約を満たす
-/
lemma zero_tax_sustainable (rich poor : Agent) :
    let sys : InstitutionalDesign :=
      { τ := 0, G := 0, τ_nonneg := le_refl 0,
        τ_lt_one := by norm_num, G_nonneg := le_refl 0 }
    isFiscalSustainable sys rich poor := by
  simp [isFiscalSustainable, agentProduction, optimalEffort]

/-! ## 主定理 -/

/--
  「最適経済制度の存在定理」

  財政サステナブルであり、かつ社会的厚生（全体の幸福）を最大化する
  『最適な税率 τ* と 給付 G* 』の組み合わせ（最適アーキテクチャ）が存在する。

  **Witness**: τ=0, G=0
  - これは「給付なし・課税なし」の状態で、インセンティブが完全に保存される。
  - 財政制約は 0 ≥ 0 で自明に成立。
  - 任意の sustainable な制度の厚生は W ≤ (1/2)(1-τ²)(Ar²+Ap²) ≤ (1/2)(Ar²+Ap²) を満たす。

  **注意**: h_disparity は将来の一意性定理・Pareto改善定理への拡張用。
-/
theorem exists_optimal_institution
    (rich poor : Agent)
    (h_disparity : poor.ability < rich.ability) :
    ∃ (best : InstitutionalDesign),
      isFiscalSustainable best rich poor ∧
      ∀ (other : InstitutionalDesign), isFiscalSustainable other rich poor →
        socialWelfare other rich poor ≤ socialWelfare best rich poor := by
  -- Witness: τ=0, G=0
  let best : InstitutionalDesign :=
    { τ := 0
      G := 0
      τ_nonneg := le_refl 0
      τ_lt_one := by norm_num
      G_nonneg := le_refl 0 }
  refine ⟨best, ?_, ?_⟩
  · -- isFiscalSustainable best
    exact zero_tax_sustainable rich poor
  · -- 最大性: ∀ other sustainable, W(other) ≤ W(best)
    intro other hother
    have h_best_welfare : socialWelfare best rich poor =
        (1 / 2) * (rich.ability ^ 2 + poor.ability ^ 2) :=
      zero_tax_welfare rich poor
    rw [h_best_welfare]
    have h_ub := welfare_upper_bound other rich poor hother
    have h_tau_sq : other.τ ^ 2 ≥ 0 := sq_nonneg _
    have h_sum_pos : rich.ability ^ 2 + poor.ability ^ 2 > 0 := by
      positivity
    nlinarith [other.τ_nonneg, other.τ_lt_one]

end OptimalEconomy
