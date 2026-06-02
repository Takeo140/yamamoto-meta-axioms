import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-- マクロ経済の状態ベクトル -/
structure MacroEconomicState where
  privateCapital : ℝ   -- 民間資本（投資に回せる私有財産・インフラ）
  totalFactorProd : ℝ  -- 全要素生産性（技術革新、分業の効率性 A ≥ 0）
  laborSupply : ℝ      -- 労働投入量 (L ≥ 0)
  workIncentive : ℝ    -- 労働・イノベーションへのインセンティブ (≤ 0 で社会麻痺)
  regimeStability : ℝ  -- 体制の持続可能性・社会の安定度

/-- 経済体制（イデオロギー）の型クラス -/
class EconomicRegime (α : Type) where
  runEconomy : α → MacroEconomicState → MacroEconomicState
  isViable : α → MacroEconomicState → Prop

/- ==========================================
   1. 共産主義体制モデル (Communism)
   ========================================== -/
structure Communism where
  centralPlanEfficiency : ℝ -- 中央計画の効率性（歴史的には極めて低迷）

instance : EconomicRegime Communism where
  runEconomy := fun model current =>
    { privateCapital := 0,                     -- 私有財産および民間資本の強制的廃止
      totalFactorProd := 0,                    -- 市場競争と分業の否定による技術の停滞・喪失
      laborSupply := current.laborSupply,
      workIncentive := -5.0,                   -- 「能力に応じて働き、必要に応じて受け取る」ことによるモラルハザード
      regimeStability := current.regimeStability - 50.0 -- 経済停滞を隠蔽・統制するための抑圧コスト
    }
  isViable := fun _ state =>
    state.privateCapital > 0 ∧ state.totalFactorProd > 0 ∧ state.workIncentive > 0 ∧ state.regimeStability > 0

/- ==========================================
   2. 資本主義体制モデル (Capitalism)
   ========================================= -/
structure Capitalism where
  savingRate : ℝ      -- 貯蓄率（マックス・ウェーバー的規律に基づく「分度」：0 < s < 1）
  investmentEff : ℝ   -- 投資効率（「推譲」による資本の次世代へのフィードバック：0 < i）

instance : EconomicRegime Capitalism where
  runEconomy := fun model current =>
    -- 経済全体の付加価値（利潤）の創出: Y = L * (1 + A)
    let aggregateProfit := current.laborSupply * (1 + current.totalFactorProd)
    { privateCapital := current.privateCapital + (aggregateProfit * model.savingRate * model.investmentEff), -- 利潤の再投資サイクル
      totalFactorProd := current.totalFactorProd + 0.2,                                                      -- 競争によるイノベーション
      laborSupply := current.laborSupply,
      workIncentive := current.workIncentive + 1.0,                                                          -- 私有財産保護によるインセンティブ向上
      regimeStability := current.regimeStability + 5.0                                                       -- 富の蓄積による体制の安定
    }
  isViable := fun _ state =>
    state.privateCapital > 0 ∧ state.workIncentive > 0 ∧ state.regimeStability > 0


/- ==========================================
   経済学の基本定理（Mathlibによる検証）
   ========================================== -/

/--
  定理 (共産主義の構造的破綻)：
  私有財産（利潤）と市場メカニズムを否定する共産主義体制は、
  どのような初期状態からスタートしても、定義上、次世代で確実にシステム崩壊（不可逆）を迎える。
-/
theorem communism_leads_to_structural_collapse 
    (init : MacroEconomicState) 
    (regime : Communism) :
    ¬ (EconomicRegime.isViable regime (EconomicRegime.runEconomy regime init)) := by
  intro h
  -- 体制維持の生存条件（全ての指標が正）を分解
  rcases h with ⟨h_priv, _, _, _⟩
  -- 共産主義の遷移関数を展開すると、privateCapital := 0 となる
  dsimp [EconomicRegime.runEconomy] at h_priv
  -- 0 > 0 という論理バグ（矛盾）を Mathlib の linarith が検出して反証完了
  linarith

/--
  定理 (資本主義の持続成長)：
  適切な貯蓄（規律）と投資（循環）が行われ、正の利潤が生まれている資本主義体制は、
  初期状態が健全である限り、経済を自律的に発展・維持させる。
-/
theorem capitalism_leads_to_sustained_growth 
    (init : MacroEconomicState) 
    (regime : Capitalism)
    (h_init_cap : init.privateCapital > 0)
    (h_init_inc : init.workIncentive > 0)
    (h_init_stab : init.regimeStability > 0)
    (h_rates : regime.savingRate > 0 ∧ regime.investmentEff > 0)
    (h_positive_growth : init.laborSupply * (1 + init.totalFactorProd) > 0) :
    EconomicRegime.isViable regime (EconomicRegime.runEconomy regime init) := by
  -- 資本主義の生存条件を満たしていることを示す
  refine ⟨?_, ?_, ?_⟩
  · dsimp [EconomicRegime.runEconomy]
    -- 資本更新: init.privateCapital + (profit * s * i)
    -- すべての要素が正であるため、Mathlib の positivity タクティクが正であることを保証
    have h_investment_loop : (init.laborSupply * (1 + init.totalFactorProd)) * regime.savingRate * regime.investmentEff > 0 := by
      positivity
    linarith
  · dsimp [EconomicRegime.runEconomy]
    -- インセンティブ更新: init.workIncentive + 1.0 > 0
    linarith
  · dsimp [EconomicRegime.runEconomy]
    -- 体制安定度更新: init.regimeStability + 5.0 > 0
    linarith
