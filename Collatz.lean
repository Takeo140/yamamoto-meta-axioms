import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-!
# Collatz Structural Properties in Standard Nat
# 整数系（Nat）におけるコラッツ構造の厳密な性質証明

`axiom` や `sorry` を一切排除し、Lean 4の標準的な自然数（Nat）の公理系の上で
完全にコンパイルが通るように調整した決定版のコードです。
-/

-- ─────────────────────────────────────────────────────────────────────────────
-- σ : ℕ → ℕ  （コラッツ写像の定義）
-- ─────────────────────────────────────────────────────────────────────────────

def sigma (n : Nat) : Nat :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

-- ─────────────────────────────────────────────────────────────────────────────
-- 反復列  σᵏ(N)
-- ─────────────────────────────────────────────────────────────────────────────

def collatz_seq (N : Nat) : Nat → Nat
  | 0     => N
  | n + 1 => sigma (collatz_seq N n)

-- ─────────────────────────────────────────────────────────────────────────────
-- 整数系（Nat）における構造的定理の証明
-- ─────────────────────────────────────────────────────────────────────────────

-- 1. σ は ℕ⁺（0より大きい自然数）において閉じている
theorem sigma_closed (n : Nat) (h : n > 0) : sigma n > 0 := by
  simp only [sigma]
  split_ifs with heven <;> omega

-- 2. すべての軌道項は 1 以上になる
theorem collatz_ge_one (N : Nat) (h : N > 0) (k : Nat) :
    collatz_seq N k ≥ 1 := by
  induction k with
  | zero => simp [collatz_seq]; omega
  | succ n ih =>
      rw [collatz_seq]
      apply sigma_closed
      omega

-- 3. 奇数ステップの出力は絶対に 3 で割り切れない（ループ制限構造）
theorem odd_step_not_div3 (n : Nat) : (3 * n + 1) % 3 ≠ 0 := by
  omega

-- 4. 奇数は不動点（σ(n) = n）にならない
theorem sigma_no_odd_fixpoint (n : Nat) (hodd : n % 2 ≠ 0) :
    sigma n ≠ n := by
  simp only [sigma]
  split_ifs with heven
  · contradiction
  · omega

-- 5. 奇数ステップの後には、必ず偶数が生成される
theorem odd_step_even (n : Nat) (hodd : n % 2 ≠ 0) :
    sigma n % 2 = 0 := by
  simp only [sigma]
  split_ifs with heven
  · contradiction
  · omega

-- 6. 偶数ステップは、正の整数において必ず厳密に減少する
theorem even_step_decreases (n : Nat) (heven : n % 2 = 0) (h : n > 0) :
    sigma n < n := by
  simp only [sigma]
  split_ifs with he
  · omega
  · contradiction

-- 7. 2ステップ収縮定理（ユーザーさんの元のコメントの数式を厳密に証明）
-- 奇数 n ≥ 3 に対して、2ステップ進んだ値は必ず 2n より小さくなる（上界の制御）
theorem two_step_contraction (n : Nat) (hodd : n % 2 ≠ 0) (h : n ≥ 3) :
    sigma (sigma n) < 2 * n := by
  simp only [sigma]
  split_ifs with h1 h2
  · contradiction
  · omega
  · omega
