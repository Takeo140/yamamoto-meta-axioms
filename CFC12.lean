import Mathlib.Data.Real.Basic

/-!
# フロンガス（CFC-12）の熱加水分解および消石灰中和の化学量論的モデル
化学反応式:
1. 熱分解: CCl₂F₂ + 2H₂O → CO₂ + 2HCl + 2HF
2. 中和:   2HCl + 2HF + 2Ca(OH)₂ → 2CaCl₂ + 2CaF₂ + 4H₂O
総合反応: CCl₂F₂ + 2Ca(OH)₂ → CO₂ + 2CaCl₂ + 2CaF₂ + 2H₂O
-/

structure ChemicalState where
  cfc : ℝ      -- CCl₂F₂ の物質量 (mol)
  ca_oh2 : ℝ   -- Ca(OH)₂ の物質量 (mol)
  co2 : ℝ      -- CO₂ の物質量 (mol)
  cacl2 : ℝ    -- CaCl₂ の物質量 (mol)
  caf2 : ℝ     -- CaF₂ の物質量 (mol)
  h2o : ℝ      -- H₂O の物質量 (mol)
  temp : ℝ     -- 反応温度 (℃)

/-- 反応進行の制約条件（温度が1200℃以上、かつ十分な消石灰が存在すること） -/
def ReactionCondition (s : ChemicalState) : Prop :=
  s.temp ≥ 1200 ∧ s.ca_oh2 ≥ 2 * s.cfc

/-- 化学反応の実行（完全分解および完全中和） -/
def runReaction (s : ChemicalState) (h : ReactionCondition s) : ChemicalState :=
  { cfc    := 0,
    ca_oh2 := s.ca_oh2 - 2 * s.cfc,
    co2    := s.co2 + s.cfc,
    cacl2  := s.cacl2 + s.cfc,
    caf2   := s.caf2 + s.cfc,
    h2o    := s.h2o + 2 * s.cfc,
    temp   := s.temp }

/-- 定理：制約条件を満たすとき、反応後のフロンガスは完全にゼロになる -/
theorem cfc_completely_destroyed (s : ChemicalState) (h : ReactionCondition s) :
  (runReaction s h).cfc = 0 := by
  rfl

/-- 定理：炭素原子数（C）の保存則 -/
theorem carbon_conservation (s : ChemicalState) (h : ReactionCondition s) :
  (runReaction s h).cfc + (runReaction s h).co2 = s.cfc + s.co2 := by
  dsimp [runReaction]
  ring

/-- 定理：カルシウム原子数（Ca）の保存則 -/
theorem calcium_conservation (s : ChemicalState) (h : ReactionCondition s) :
  (runReaction s h).ca_oh2 + (runReaction s h).cacl2 + (runReaction s h).caf2 =
  s.ca_oh2 + s.cacl2 + s.caf2 := by
  dsimp [runReaction]
  ring

/-- 定理：フッ素原子数（F）の保存則 -/
theorem fluorine_conservation (s : ChemicalState) (h : ReactionCondition s) :
  2 * (runReaction s h).cfc + 2 * (runReaction s h).caf2 = 2 * s.cfc + 2 * s.caf2 := by
  dsimp [runReaction]
  ring

/-- 定理：塩素原子数（Cl）の保存則 -/
theorem chlorine_conservation (s : ChemicalState) (h : ReactionCondition s) :
  2 * (runReaction s h).cfc + 2 * (runReaction s h).cacl2 = 2 * s.cfc + 2 * s.cacl2 := by
  dsimp [runReaction]
  ring
