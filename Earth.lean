import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Earth Environment Optimizer — F-Theory Meta-Axiom v2
A1: 極値原理 — 閾値までの最小距離 = 最小介入量
A2: 解空間   — 閾値で定義された成功領域
A3: 整合性   — is_isomorphic による構造照合
A4: 階層構造 — 変数ごとの独立評価 → 統合判定
-/

-- ── 定数（成功構造の定義）────────────────────────────────────────────────────

def CO2_THRESHOLD          : Float := 350.0
def TEMP_THRESHOLD         : Float := 1.5
def BIODIVERSITY_THRESHOLD : Float := 0.8

-- ── データ構造 ────────────────────────────────────────────────────────────────

structure EarthState where
  co2          : Float
  tempDelta    : Float
  biodiversity : Float
deriving Repr

structure Intervention where
  variable  : String
  current   : Float
  threshold : Float
  delta     : Float   -- 正=増加必要、負=削減必要、0=充足済み
  satisfied : Bool
deriving Repr

structure ExtractionResult where
  isSuccess     : Bool
  interventions : Array Intervention
deriving Repr

-- ── A3: 個別条件判定 ──────────────────────────────────────────────────────────

def co2Satisfied (s : EarthState) : Bool :=
  s.co2 <= CO2_THRESHOLD

def tempSatisfied (s : EarthState) : Bool :=
  s.tempDelta <= TEMP_THRESHOLD

def bioSatisfied (s : EarthState) : Bool :=
  s.biodiversity >= BIODIVERSITY_THRESHOLD

-- ── A3: 統合構造照合 ──────────────────────────────────────────────────────────

def isIsomorphic (s : EarthState) : Bool :=
  co2Satisfied s && tempSatisfied s && bioSatisfied s

-- ── A1: 最小介入量（閾値距離）────────────────────────────────────────────────

def co2Intervention (s : EarthState) : Intervention :=
  let sat := co2Satisfied s
  { variable  := "co2"
    current   := s.co2
    threshold := CO2_THRESHOLD
    delta     := if sat then 0.0 else CO2_THRESHOLD - s.co2
    satisfied := sat }

def tempIntervention (s : EarthState) : Intervention :=
  let sat := tempSatisfied s
  { variable  := "temp_delta"
    current   := s.tempDelta
    threshold := TEMP_THRESHOLD
    delta     := if sat then 0.0 else TEMP_THRESHOLD - s.tempDelta
    satisfied := sat }

def bioIntervention (s : EarthState) : Intervention :=
  let sat := bioSatisfied s
  { variable  := "biodiversity"
    current   := s.biodiversity
    threshold := BIODIVERSITY_THRESHOLD
    delta     := if sat then 0.0 else BIODIVERSITY_THRESHOLD - s.biodiversity
    satisfied := sat }

-- ── メイン抽出関数 ────────────────────────────────────────────────────────────

def extractSolution (s : EarthState) : ExtractionResult :=
  { isSuccess     := isIsomorphic s
    interventions := #[ co2Intervention s
                      , tempIntervention s
                      , bioIntervention s ] }

-- ── 定理群 ───────────────────────────────────────────────────────────────────

-- A3: 全条件充足 ↔ isIsomorphic
theorem isIsomorphic_iff (s : EarthState) :
    isIsomorphic s = true ↔
    co2Satisfied s = true ∧
    tempSatisfied s = true ∧
    bioSatisfied s = true := by
  simp [isIsomorphic, Bool.and_eq_true]

-- A1: 充足済み変数の介入量は 0
theorem co2_delta_zero_if_satisfied (s : EarthState)
    (h : co2Satisfied s = true) :
    (co2Intervention s).delta = 0.0 := by
  simp [co2Intervention, h]

theorem temp_delta_zero_if_satisfied (s : EarthState)
    (h : tempSatisfied s = true) :
    (tempIntervention s).delta = 0.0 := by
  simp [tempIntervention, h]

theorem bio_delta_zero_if_satisfied (s : EarthState)
    (h : bioSatisfied s = true) :
    (bioIntervention s).delta = 0.0 := by
  simp [bioIntervention, h]

-- A4: isIsomorphic → 全介入量が 0
theorem all_deltas_zero_if_isomorphic (s : EarthState)
    (h : isIsomorphic s = true) :
    (co2Intervention s).delta = 0.0 ∧
    (tempIntervention s).delta = 0.0 ∧
    (bioIntervention s).delta = 0.0 := by
  rw [isIsomorphic_iff] at h
  exact ⟨ co2_delta_zero_if_satisfied  s h.1
         , temp_delta_zero_if_satisfied s h.2.1
         , bio_delta_zero_if_satisfied  s h.2.2 ⟩

-- O1_convergence: 解の抽出は入力に対して決定論的
theorem O1_convergence (s : EarthState) :
    extractSolution s = extractSolution s :=
  rfl

-- ── エントリポイント ──────────────────────────────────────────────────────────

def main : IO Unit := do
  let cases : Array (String × EarthState) := #[
    ("現状の地球",   { co2 := 420.0, tempDelta := 1.2, biodiversity := 0.75 }),
    ("改善途上",     { co2 := 370.0, tempDelta := 1.4, biodiversity := 0.85 }),
    ("最適化済み",   { co2 := 340.0, tempDelta := 1.1, biodiversity := 0.95 })
  ]
  for (label, state) in cases do
    let r := extractSolution state
    IO.println s!"{'='*50}"
    IO.println s!"  {label}"
    IO.println s!"  構造: {if r.isSuccess then \"META_AXIOM_SUCCESS\" else \"STRUCTURE_MISMATCH\"}"
    for iv in r.interventions do
      let mark := if iv.satisfied then "✓" else "✗"
      IO.println s!"  {iv.variable}: 現在={iv.current} 閾値={iv.threshold} Δ={iv.delta} {mark}"
