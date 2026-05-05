import Mathlib.Data.Rat.Basic
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Matrix.Basic

/-!
# マルクス経済学の内部矛盾：完全形式化 (証明完結版)
-/

namespace MarxCritique

-- ================================================================
-- §1. 転形問題
-- ================================================================

structure Sector where c v s : ℚ

def marxValue    (σ : Sector) : ℚ := σ.c + σ.v + σ.s
def avgProfitRate (σ₁ σ₂ : Sector) : ℚ :=
  (σ₁.s + σ₂.s) / (σ₁.c + σ₁.v + σ₂.c + σ₂.v)
def prodPrice    (σ : Sector) (r : ℚ) : ℚ := (σ.c + σ.v) * (1 + r)

theorem transformation_problem :
    let σ₁ : Sector := ⟨80, 20, 20⟩
    let σ₂ : Sector := ⟨20, 80, 80⟩
    let r := avgProfitRate σ₁ σ₂
    prodPrice σ₁ r / marxValue σ₁ ≠ prodPrice σ₂ r / marxValue σ₂ := by
  native_decide

-- ================================================================
-- §2. Steedman 負値定理
-- ================================================================

theorem steedman_negative_values :
    let λ_A : ℚ := 11/4; let λ_B : ℚ := -1/4
    2 * λ_A + 2 * λ_B = 5 ∧ λ_A + 3 * λ_B = 2 ∧ λ_B < 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

theorem steedman_solution_unique :
    ∀ λ_A λ_B : ℚ, 2 * λ_A + 2 * λ_B = 5 → λ_A + 3 * λ_B = 2 →
    λ_A = 11/4 ∧ λ_B = -1/4 := fun _ _ h1 h2 => ⟨by linarith, by linarith⟩

-- ================================================================
-- §3. Sraffa 価値冗長性定理
-- ================================================================

namespace Sraffa

open Matrix Finset

-- ──────────────────────────────────────────────────────────────
-- §3a. 2部門具体例
-- ──────────────────────────────────────────────────────────────

def A₂ : Matrix (Fin 2) (Fin 2) ℚ
  | 0, 0 => 0;    | 0, 1 => 1/3
  | 1, 0 => 1/2;  | 1, 1 => 0

def l₂ : Fin 2 → ℚ := ![1, 1]
def λ₂ : Fin 2 → ℚ := ![9/5, 8/5]
def p₂ : Fin 2 → ℚ := ![40/19, 35/19]

@[simp] lemma A₂_00 : A₂ 0 0 = 0   := rfl
@[simp] lemma A₂_01 : A₂ 0 1 = 1/3 := rfl
@[simp] lemma A₂_10 : A₂ 1 0 = 1/2 := rfl
@[simp] lemma A₂_11 : A₂ 1 1 = 0   := rfl
@[simp] lemma l₂_0  : l₂ 0 = 1     := rfl
@[simp] lemma l₂_1  : l₂ 1 = 1     := rfl
@[simp] lemma λ₂_0  : λ₂ 0 = 9/5   := rfl
@[simp] lemma λ₂_1  : λ₂ 1 = 8/5   := rfl
@[simp] lemma p₂_0  : p₂ 0 = 40/19 := rfl
@[simp] lemma p₂_1  : p₂ 1 = 35/19 := rfl

theorem labor_values_satisfy :
    ∀ j : Fin 2, λ₂ j = ∑ i : Fin 2, λ₂ i * A₂ i j + l₂ j := by
  intro j; fin_cases j <;> simp [Fin.sum_univ_two] <;> norm_num

theorem labor_values_unique :
    ∀ μ : Fin 2 → ℚ,
      (∀ j : Fin 2, μ j = ∑ i : Fin 2, μ i * A₂ i j + l₂ j) → μ = λ₂ := by
  intro μ hμ
  have eq0 : μ 0 = μ 1 * (1/2) + 1 := by
    have h := hμ 0; simp [Fin.sum_univ_two] at h; linarith
  have eq1 : μ 1 = μ 0 * (1/3) + 1 := by
    have h := hμ 1; simp [Fin.sum_univ_two] at h; linarith
  funext j; fin_cases j <;> simp [λ₂] <;> linarith

theorem sraffa_prices_satisfy :
    ∀ j : Fin 2,
      p₂ j = (1 + 1/5) * ∑ i : Fin 2, p₂ i * A₂ i j + 1 * l₂ j := by
  intro j; fin_cases j <;> simp [Fin.sum_univ_two] <;> norm_num

theorem sraffa_prices_unique :
    ∀ q : Fin 2 → ℚ,
      (∀ j : Fin 2, q j = (1 + 1/5) * ∑ i : Fin 2, q i * A₂ i j + 1 * l₂ j) →
      q = p₂ := by
  intro q hq
  have eq0 : q 0 = q 1 * (3/5) + 1 := by
    have h := hq 0; simp [Fin.sum_univ_two] at h; linarith
  have eq1 : q 1 = q 0 * (2/5) + 1 := by
    have h := hq 1; simp [Fin.sum_univ_two] at h; linarith
  funext j; fin_cases j <;> simp [p₂] <;> linarith

/-- 主定理: 価格比 ≠ 価値比 -/
theorem prices_not_proportional_to_values :
    p₂ 0 * λ₂ 1 ≠ p₂ 1 * λ₂ 0 := by norm_num [p₂, λ₂]

-- ──────────────────────────────────────────────────────────────
-- §3b. n部門一般定理
-- ──────────────────────────────────────────────────────────────

variable {n : ℕ} [NeZero n]

structure Economy where
  A : Matrix (Fin n) (Fin n) ℚ
  l : Fin n → ℚ

def IsSraffaPrice (e : Economy) (p : Fin n → ℚ) (r w : ℚ) : Prop :=
  ∀ j, p j = (1 + r) * ∑ i, p i * e.A i j + w * e.l j

def IsLaborValue (e : Economy) (λv : Fin n → ℚ) : Prop :=
  ∀ j, λv j = ∑ i, λv i * e.A i j + e.l j

/-- 構造的価値冗長性: IsSraffaPrice の型にλは現れない -/
theorem structural_value_redundancy
    (e : Economy) (p : Fin n → ℚ) (r w : ℚ)
    (hp : IsSraffaPrice e p r w) :
    ∀ (λ₁ λ₂ : Fin n → ℚ),
      IsLaborValue e λ₁ → IsLaborValue e λ₂ → IsSraffaPrice e p r w :=
  fun _ _ _ _ => hp

-- ──────────────────────────────────────────────────────────────
-- §3c. 存在・一意性 (Matrix.nonsing_inv による閉形式)
-- ──────────────────────────────────────────────────────────────

/-
IsSraffaPrice e p r w
  ↔ ∀ j, Σᵢ pᵢ (δᵢⱼ - (1+r)Aᵢⱼ) = w lⱼ
  ↔ vecMul p M = b        (M := I - (1+r)A, b j := w lⱼ)

det M ≠ 0 のとき:
  存在: p* = vecMul b M⁻¹, vecMul p* M = vecMul b (M⁻¹M) = vecMul b 1 = b
  一意: p = vecMul p 1 = vecMul p (MM⁻¹) = vecMul (vecMul p M) M⁻¹ = vecMul b M⁻¹
-/

-- 補題: 和の書き換え
private lemma sum_rewrite (p : Fin n → ℚ) (A : Matrix (Fin n) (Fin n) ℚ) (r : ℚ) (j : Fin n) :
    ∑ i : Fin n, p i * ((if i = j then (1 : ℚ) else 0) - (1 + r) * A i j)
    = p j - (1 + r) * ∑ i : Fin n, p i * A i j := by
  have h1 : ∑ i : Fin n, p i * (if i = j then (1 : ℚ) else 0) = p j := by
    simp [mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ]
  have h2 : ∑ i : Fin n, p i * ((1 + r) * A i j) = (1 + r) * ∑ i : Fin n, p i * A i j := by
    rw [mul_sum]; congr 1; funext i; ring
  calc ∑ i : Fin n, p i * ((if i = j then 1 else 0) - (1 + r) * A i j)
      = ∑ i : Fin n, (p i * (if i = j then 1 else 0) - p i * ((1 + r) * A i j)) := by
          congr 1; funext i; ring
    _ = ∑ i : Fin n, p i * (if i = j then 1 else 0) -
        ∑ i : Fin n, p i * ((1 + r) * A i j) := sum_sub_distrib
    _ = p j - (1 + r) * ∑ i : Fin n, p i * A i j := by rw [h1, h2]

-- IsSraffaPrice ↔ vecMul p M = b
private lemma sraffa_iff_vecMul (e : Economy) (p : Fin n → ℚ) (r w : ℚ) :
    IsSraffaPrice e p r w ↔
    vecMul p ((1 : Matrix (Fin n) (Fin n) ℚ) - (1 + r) • e.A) = fun j => w * e.l j := by
  simp only [IsSraffaPrice, vecMul, dotProduct,
             Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  constructor
  · intro h; funext j
    linarith [sum_rewrite p e.A r j, h j]
  · intro h j
    linarith [sum_rewrite p e.A r j, congr_fun h j]


theorem sraffa_price_exists_unique
    (e : Economy) (r w : ℚ) (hw : 0 < w)
    (hDet : ((1 : Matrix (Fin n) (Fin n) ℚ) - (1 + r) • e.A).det ≠ 0) :
    ∃! p : Fin n → ℚ, IsSraffaPrice e p r w := by
  let M := (1 : Matrix (Fin n) (Fin n) ℚ) - (1 + r) • e.A
  let b : Fin n → ℚ := fun j => w * e.l j
  simp_rw [sraffa_iff_vecMul]
  refine ⟨vecMul b M⁻¹, ?_, ?_⟩
  · -- 存在: vecMul (vecMul b M⁻¹) M = b
    rw [← vecMul_mul, Matrix.nonsing_inv_mul M hDet, vecMul_one]
  · -- 一意性
    intro p hp
    calc p = vecMul p 1              := (vecMul_one p).symm
         _ = vecMul p (M * M⁻¹)     := by rw [Matrix.mul_nonsing_inv M hDet]
         _ = vecMul (vecMul p M) M⁻¹ := by rw [vecMul_mul]
         _ = vecMul b M⁻¹            := by rw [hp]

end Sraffa
end MarxCritique
