-- Houtoku.lean
-- License: CC-BY-4.0 (for academic dissemination)
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
/-!
# 報徳仕法の形式化
このモジュールは、二宮尊徳の「報徳仕法」における経済成長モデルを定義します。
「分度」による支出の固定と、「推譲」による再投資が、
生産性（石高）の指数関数的な成長をもたらすことを示唆します。
-/
/-- 報徳経済の状態を表す構造体 -/
structure HoutokuState where
  /-- 現在の生産能力（石高 / Productivity） -/
  productivity : ℝ
  /-- 蓄積された資本（報徳金 / Capital） -/
  capital : ℝ
  -- deriving Show は ℝ に Show インスタンスが無いため削除

/-- 仕法のパラメータ -/
structure HoutokuParams where
  /-- 分度比率（Bundo: 収入のうち自己消費に回す割合） -/
  bundo_ratio : ℝ
  /-- 推譲効率（Reinvestment Efficiency: 再投資が生産性に与える影響係数） -/
  efficiency : ℝ
  /-- 分度比率の妥当性条件 (0 < bundo < 1) -/
  h_bundo : 0 < bundo_ratio ∧ bundo_ratio < 1
  /-- 効率は正である -/
  h_eff : 0 < efficiency

/-- 1サイクル（1年）の経済発展関数 -/
def step (p : HoutokuParams) (s : HoutokuState) : HoutokuState :=
  let income := s.productivity
  let bundo  := p.bundo_ratio * income
  let suijo  := income - bundo
  { productivity := s.productivity + p.efficiency * suijo,
    capital      := s.capital + suijo }

/-- 報徳仕法による成長の定理：推譲が正である限り、次期の生産性は今期を上回る -/
theorem growth_guaranteed (p : HoutokuParams) (s : HoutokuState)
    (h_pos : 0 < s.productivity) :
    s.productivity < (step p s).productivity := by
  simp only [step]
  -- simp 展開後のゴール:
  --   s.productivity < s.productivity + p.efficiency * (s.productivity - p.bundo_ratio * s.productivity)
  -- 増分が正であることを示す
  have h_inc : 0 < p.efficiency * (s.productivity - p.bundo_ratio * s.productivity) := by
    have heq : s.productivity - p.bundo_ratio * s.productivity =
               (1 - p.bundo_ratio) * s.productivity := by ring
    rw [heq]
    apply mul_pos p.h_eff
    apply mul_pos
    · linarith [p.h_bundo.2]
    · exact h_pos
  linarith

/--
  長期的な最適化定式化 (Meta-Axiom of Optimization)
  報徳仕法は、消費(Bundo)を定数化することで、
  時間(t)に対する生産性(P)の微分を最大化するシステムである。
-/
noncomputable def optimal_growth_rate (p : HoutokuParams) : ℝ :=
  p.efficiency * (1 - p.bundo_ratio)
-- 結論：生産性 P(t) は P(0) * exp(optimal_growth_rate * t) の形態で成長する。
