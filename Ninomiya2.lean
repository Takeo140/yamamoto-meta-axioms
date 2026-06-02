import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-- 経済状態ベクトル。Mathlibの実数 ℝ をベースに構築 -/
structure EconomicState where
  capital : ℝ         -- 資本（道具、インフラ、共同基金）
  technology : ℝ      -- 技術・イノベーション水準 (A ≥ 0)
  labor : ℝ           -- 労働投入量 (L ≥ 0)
  incentive : ℝ       -- 人間の労働・創造意欲 (これが 0 以下になると機能停止)
  socialStability : ℝ -- 社会の持続可能性・生存指標

/-- 経済システムを定義する型クラス -/
class EconomicSystem (α : Type) where
  nextState : α → EconomicState → EconomicState
  isSustainable : α → EconomicState → Prop

/- ==========================================
   1. 安藤昌益・ポル・ポト モデル (利潤・分業の否定)
   ========================================== -/
inductive ShoekiModel where
  | chokou -- 直耕・原始化の強制

instance : EconomicSystem ShoekiModel where
  nextState := fun _ current =>
    { capital := 0,                     -- 資本（私有・蓄積・余剰）の強制的解体
      technology := 0,                  -- 知識階級・分業の否定による技術の忘却
      labor := current.labor,
      incentive := -1,                  -- 成果獲得のインセンティブが完全に崩壊
      socialStability := current.socialStability - 100 } -- 都市解体と飢餓による社会の壊滅
  isSustainable := fun _ state =>
    state.capital > 0 ∧ state.technology > 0 ∧ state.incentive > 0 ∧ state.socialStability > 0

/- ==========================================
   2. 二宮尊徳 モデル (利潤の公認・分度・推譲)
   ========================================= -/
structure SontokuModel where
  bundo : ℝ  -- 分度：生産力に応じた適切な消費の閾値
  suijo : ℝ  -- 推譲：利潤（余剰）を次の発展へ回す「再投資率」 (0 < suijo)

instance : EconomicSystem SontokuModel where
  nextState := fun model current =>
    -- 正当な利潤（マクロ経済における付加価値）の発生
    -- Y = L * (1 + A) - Bundo
    let profit := current.labor * (1 + current.technology) - model.bundo
    { capital := current.capital + (profit * model.suijo), -- 推譲による資本の蓄積サイクル
      technology := current.technology + 0.1,             -- 投資による技術・インフラの発展
      labor := current.labor,
      incentive := current.incentive + 0.5,               -- 成果が認められることによる意欲向上
      socialStability := current.socialStability + 10 }    -- 社会の持続的な再生
  isSustainable := fun _ state =>
    state.capital > 0 ∧ state.incentive > 0 ∧ state.socialStability > 0


/- ==========================================
   Mathlibベースの定理証明
   ========================================== -/

/--
  定理：安藤昌益（ポル・ポト）的アプローチは、どのような初期状態からスタートしても、
  次の段階で必ず社会の壊滅（不持続性）を招く。
  (Mathlibの linarith タクティクによる 0 > 0 の矛盾導出)
-/
theorem shoeki_leads_to_collapse 
    (init : EconomicState) 
    (m : ShoekiModel) :
    ¬ (EconomicSystem.isSustainable m (EconomicSystem.nextState m init)) := by
  intro h
  -- 持続可能条件を分解 (capital > 0 ∧ technology > 0 ∧ ...)
  rcases h with ⟨h_cap, _, _, _⟩
  -- 昌益モデルの実装を展開。capital := 0 となるため、 0 > 0 という矛盾が生じる
  dsimp [EconomicSystem.nextState] at h_cap
  linarith

/--
  定理：二宮尊徳的アプローチ（分度と推譲）は、初期状態が健全であり、
  かつ正当な利潤（余剰）が生まれている限り、次世代の社会を確実に持続・再生させる。
  (Mathlibの positivity および linarith による証明)
-/
theorem sontoku_leads_to_revival 
    (init : EconomicState) 
    (m : SontokuModel)
    (h_init_cap : init.capital > 0)
    (h_init_inc : init.incentive > 0)
    (h_init_stab : init.socialStability > 0)
    (h_suijo : m.suijo > 0)
    (h_profit : init.labor * (1 + init.technology) - m.bundo > 0) :
    EconomicSystem.isSustainable m (EconomicSystem.nextState m init) := by
  -- 尊徳モデルにおける持続可能条件 (capital > 0 ∧ incentive > 0 ∧ socialStability > 0) を証明する
  refine ⟨?_, ?_, ?_⟩
  · dsimp [EconomicSystem.nextState]
    -- 資本の更新式: init.capital + (profit * m.suijo)
    -- init.capital > 0 かつ (profit * m.suijo) > 0 なので、全体として正になる
    have h_invest : (init.labor * (1 + init.technology) - m.bundo) * m.suijo > 0 := by
      positivity
    linarith
  · dsimp [EconomicSystem.nextState]
    -- インセンティブの更新式: init.incentive + 0.5
    -- init.incentive > 0 なので確実に正
    linarith
  · dsimp [EconomicSystem.nextState]
    -- 社会安定度の更新式: init.socialStability + 10
    -- init.socialStability > 0 なので確実に正
    linarith
