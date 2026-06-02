import Mathlib.Data.Real.Basic

/-!
# 触媒を用いたフロンガス（CFC-12）の低温分解および中和の化学量論的モデル

特徴:
- 高温（1200℃）を必要とせず、適切な触媒の存在下（活性化エネルギーの低下）で進行する。
- 触媒は反応前後で物質量が変化しない（不変）。
-/

structure CatalyticState where
  cfc : ℝ          -- CCl₂F₂ の物質量 (mol)
  ca_oh2 : ℝ       -- Ca(OH)₂（中和剤）の物質量 (mol)
  catalyst : ℝ     -- 触媒（例: 固体酸、酸化アルミニウム等）の物質量 (mol)
  co2 : ℝ          -- 生成される CO₂ (mol)
  cacl2 : ℝ        -- 生成される CaCl₂ (mol)
  caf2 : ℝ         -- 生成される CaF₂ (mol)
  h2o : ℝ          -- 生成される H₂O (mol)
  temp : ℝ         -- 反応温度 (℃)

/-- 触媒分解の進行条件（触媒が存在すること、温度が適切[200℃以上]であること、中和剤が十分であること） -/
def CatalyticCondition (s : CatalyticState) : Prop :=
  s.catalyst > 0 ∧ s.temp ≥ 200 ∧ s.ca_oh2 ≥ 2 * s.cfc

/-- 触媒分解反応の実行 -/
def runCatalyticReaction (s : CatalyticState) (h : CatalyticCondition s) : CatalyticState :=
  { cfc      := 0,
    ca_oh2   := s.ca_oh2 - 2 * s.cfc,
    catalyst := s.catalyst,  -- 触媒は消費されず、そのまま残る（保存）
    co2      := s.co2 + s.cfc,
    cacl2    := s.cacl2 + s.cfc,
    caf2     := s.caf2 + s.cfc,
    h2o      := s.h2o + 2 * s.cfc,
    temp     := s.temp }

/-- 定理：触媒条件を満たすとき、フロンガスは完全に分解（ゼロ化）される -/
theorem cfc_is_catalytically_destroyed (s : CatalyticState) (h : CatalyticCondition s) :
  (runCatalyticReaction s h).cfc = 0 := by
  rfl

/-- 定理：触媒の物質量が反応前後で不変（保存）であることの証明 -/
theorem catalyst_preserved (s : CatalyticState) (h : CatalyticCondition s) :
  (runCatalyticReaction s h).catalyst = s.catalyst := by
  rfl

/-- 定理：フッ素原子（F）の保存則 -/
theorem fluorine_conservation_cat (s : CatalyticState) (h : CatalyticCondition s) :
  2 * (runCatalyticReaction s h).cfc + 2 * (runCatalyticReaction s h).caf2 = 2 * s.cfc + 2 * s.caf2 := by
  dsimp [runCatalyticReaction]
  ring

/-- 定理：塩素原子（Cl）の保存則 -/
theorem chlorine_conservation_cat (s : CatalyticState) (h : CatalyticCondition s) :
  2 * (runCatalyticReaction s h).cfc + 2 * (runCatalyticReaction s h).cacl2 = 2 * s.cfc + 2 * s.cacl2 := by
  dsimp [runCatalyticReaction]
  ring

