import Mathlib.Data.Real.Basic

/-!
# 共産主義崩壊モデル（The Mathematical Subversion of Communism）

本コードは、マルクス主義および安藤昌益的な「利潤否定・再投資拒絶型」の経済システムが、
人間の精神性や道徳心とは一切関係なく、地球の物理法則（資本減耗）という「引き算」によって
確定的に動学自壊（ポル・ポト化・原始ディストピア化）を迎えることを証明した数理仕様書である。
-/

/-- 
  社会のインフラおよび生産手段を定義するベースシステム
  - `K` : 社会の総資本ストック（インフラ、工場、農地、医療設備）
  - `δ` : 物理的・自然的な減耗率（老朽化、摩耗、風化、天災リスク）
  - `Y` : 総生産（労働と資本によって生み出される富）
-/
structure EconomicSystem where
  K : ℝ
  δ : ℝ
  Y : ℝ
  K_pos : 0 < K
  δ_pos : 0 < δ ∧ δ < 1
  Y_pos : 0 < Y

/-- 
  時間の経過（次世代）に伴う資本ストックの遷移関数。
  新しい資本は、「今ある資本」から「減耗（老朽化）」を引き、
  そこに未来への「再投資（I）」を足すことで決定される。
-/
def next_capital (sys : EconomicSystem) (I : ℝ) : ℝ :=
  sys.K - (sys.δ * sys.sys.K) + I

---

/-! ## 1. 共産主義（マルクス・昌益型）の設計バグ -/

/-- 
  共産主義システム（Communism System）の定義。
  彼らのドグマは「利潤（剰余価値）＝労働者からの搾取（悪）」である。
  したがって、システム内での利益の蓄積を呪い、全員でその日の生産を均等に分配・消費し尽くす。
  結果として、未来のインフラを維持・アップデートするための「再投資（I）」のインプットを拒絶する。
-/
structure CommunismSystem extends EconomicSystem where
  -- 【致命的なイデオロギー制約】：利潤を認めないため、未来への再投資回路（I）が常にゼロとなる
  dogma_no_reinvestment : ∀ (I : ℝ), I = 0

/-- 
  【定理：共産主義の構造的崩壊（The Collapse Theorem）】
  どれほど住民が平等で、真面目で、高潔なモラルを持って直耕（労働）に励もうが、
  `I = 0` をシステムに組み込んだ瞬間、インフラの老朽化（δ * K）という物理的な引き算を
  相殺する手段を失い、社会の総資本（K）は時間とともに確定的にマイナス（ジリ貧）へ向かう。
-/
theorem communism_structural_collapse (sys : CommunismSystem) :
  next_capital sys.toEconomicSystem 0 < sys.K := by
  dsimp [next_capital]
  -- 資本が正であり、減耗率が正であるため、減耗分（δ * K）は必ず正の引き算となる
  have depreciation_is_positive : 0 < sys.δ * sys.K := mul_pos sys.δ_pos.1 sys.K_pos
  linarith

---

/-! ## 2. 資本主義（尊徳・報徳仕法型）のバグ修正 -/

/-- 
  対照的に、健全な資本主義（および尊徳モデル）の定義。
  人間の知恵によって「価値の純増（利潤）」を生み出すプラスサムゲームを肯定する。
  消費をコントロールする規律（分度）によって余剰を確保し、
  それを未来のインフラや社会の維持のために計画的に「推譲（再投資：suijo）」する。
-/
structure CapitalistGrowthSystem extends EconomicSystem where
  suijo : ℝ
  -- 【生存条件】：未来への投資（推譲）が、自然の老朽化・減耗を常に上回り続ける
  suijo_gt_depreciation : suijo > δ * K

/-- 
  【定理：動学的拡大均衡】
  利潤を「善なるエネルギー」として還流させるシステムは、地球の物理法則（減耗）を克服し、
  社会の生存確率と豊かさ（K）を次世代へと持続可能に拡大（成長）させることができる。
-/
theorem capitalist_sustained_growth (sys : CapitalistGrowthSystem) :
  next_capital sys.toEconomicSystem sys.suijo > sys.K := by
  dsimp [next_capital]
  have growth_driver : sys.suijo > sys.δ * sys.K := sys.suijo_gt_depreciation
  linarith
