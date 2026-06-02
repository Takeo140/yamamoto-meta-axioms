import Mathlib.Data.Real.Basic

/-!
# 二宮尊徳の「拡大均衡」と安藤昌益の「縮小均衡（自壊）」の数理フォーマライズ

本コードは、江戸期の二大思想家における「余剰（利潤）」の処理システムを
近代マクロ経済学の動学成長モデルとして型定義し、
「利潤の再投資（推譲）」の有無が社会の存続に与える影響を論理的に証明したものである。
-/

/-- 
  社会の富と動学特性を定義する基本構造体（マクロ経済システム）
  - `K` : 資本ストック（社会のインフラ、土地の肥沃さ、富の総量）
  - `δ` : 資本減耗率（インフラや自然が時間経過で劣化・減価償却する割合）
-/
structure EconomicSystem where
  K : ℝ
  δ : ℝ
  K_pos : 0 < K
  δ_pos : 0 < δ ∧ δ < 1

/-- 
  次世代の資本（富）を決定する遷移関数。
  次世代の富 ＝ 現世代の富 − 自然の減耗(δ * K) ＋ 未来への再投資(I)
-/
def next_capital (sys : EconomicSystem) (I : ℝ) : ℝ :=
  sys.K - (sys.δ * sys.K) + I

---

/-! ## 1. 安藤昌益セクター：再投資なき定常（自壊の定理） -/

/-- 
  安藤昌益の思想（直耕・蓄積否定）を反映したシステム。
  利潤（余剰）の発生と蓄積を悪とみなし、未来への「再投資」を一切認めない（常にゼロ）。
-/
structure ShoekiSystem extends EconomicSystem where
  no_reinvestment : ∀ (I : ℝ), I = 0

/-- 
  【定理：昌益システムの構造的自壊】
  利潤の再投資を拒絶したシステムは、人間の労働がどれほど純粋であっても、
  自然の減耗（減価償却）に耐えられず、世代を追うごとに富の総量が必ず縮小する。
-/
theorem shoeki_collapse (sys : ShoekiSystem) :
  next_capital sys.toEconomicSystem 0 < sys.K := by
  dsimp [next_capital]
  -- 資本減耗 (sys.δ * sys.K) が正の数であることを証明
  have h_dep_pos : 0 < sys.δ * sys.K := mul_pos sys.δ_pos.1 sys.K_pos
  -- Kから正の数を引いたものは、元のKより小さい（Linarithによる自動線形算術証明）
  linarith

---

/-! ## 2. 二宮尊徳セクター：分度と推譲（拡大均衡の定理） -/

/-- 
  二宮尊徳の思想（報徳仕法）を反映したシステム。
  自己の消費に規律（分度）を設け、生み出された利潤・余剰を「推譲（未来への再投資）」に回す。
  ここでの条件は、推譲（suijo）の量が、社会の自然減耗（δ * K）を上回るイノベーションを持つこと。
-/
structure SontokuSystem extends EconomicSystem where
  suijo : ℝ
  suijo_gt_dep : suijo > δ * K

/-- 
  【定理：尊徳システムの拡大均衡】
  利潤本来の意味（価値の純増）を認め、それを「推譲」として計画的に再投資するシステムは、
  自然の減耗を克服し、次世代の富の総量を確実に拡大・発展させる。
-/
theorem sontoku_growth (sys : SontokuSystem) :
  next_capital sys.toEconomicSystem sys.suijo > sys.K := by
  dsimp [next_capital]
  -- 推譲(suijo)が減耗(sys.δ * sys.K)を上回っているという公理（suijo_gt_dep）を利用
  have h_growth : sys.suijo > sys.δ * sys.K := sys.suijo_gt_dep
  -- したがって、K - 減耗 + 推譲 は K より大きくなる
  linarith
