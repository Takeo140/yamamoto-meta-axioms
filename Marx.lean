-- 1. 労働の種類を定義
inductive LaborType where
  | Simple  : LaborType
  | Complex : (specialty : String) → LaborType

-- 2. マルクス主義的な「価値」（労働時間のみ）
def MarxianValue (hours : Float) : Float :=
  1.0 * hours

-- 3. 資本主義的（現実的）な成果
-- 修正: else側を hours * 0.1 に（定数 0.1 は誤り）
structure RealityResult where
  labor        : LaborType
  hours        : Float
  breakthrough : Bool
  outputValue  : Float :=
    match labor with
    | LaborType.Simple    => hours * 1.0
    | LaborType.Complex _ => if breakthrough then hours * 10000.0 else hours * 0.1

-- 4. 論理破綻の証明
-- 修正: ∀ h は h=0 で偽になるため、存在命題（∃）として正しく定式化
-- 具体的証人: hours=1.0, 製薬ブレークスルーあり
-- MarxianValue 1.0 = 1.0  ≠  10000.0 = outputValue
theorem Marxian_Contradiction :
    ∃ (r : RealityResult), MarxianValue r.hours ≠ r.outputValue :=
  ⟨{ labor := .Complex "Pharma", hours := 1.0, breakthrough := true },
   by native_decide⟩
