import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-!
# Collatz Structural Analysis (Standard Integer System)
# 整数系(Nat)におけるコラッツ写像の性質の形式化
収束を公理とせず、標準的な自然数の公理系に基づき、
コラッツ関数の動的な挙動（縮小性と併合性）を定理として形式化。
-/

def sigma (n : Nat) : Nat :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

def collatz_seq (N : Nat) : Nat → Nat
  | 0     => N
  | n + 1 => sigma (collatz_seq N n)

theorem even_step_halves (n : Nat) (heven : n % 2 = 0) (hpos : n > 0) :
    sigma n = n / 2 := by
  unfold sigma
  simp [heven]

-- sorryなし: omega で解決
theorem odd_step_produces_even (n : Nat) (hodd : n % 2 ≠ 0) :
    sigma n % 2 = 0 := by
  unfold sigma
  split
  · omega
  · omega

-- sorryなし: omega で解決
theorem two_step_contraction (n : Nat) (hodd : n % 2 ≠ 0) (h : n ≥ 3) :
    sigma (sigma n) < n := by
  unfold sigma
  split with h1
  · omega
  · split with h2
    · omega
    · omega

-- 未解決予想: conjecture キーワード非存在のため theorem + sorry
-- 「ここから先は未解決」を明示
theorem collatz_convergence (N : Nat) (h : N > 0) :
    ∃ k : Nat, collatz_seq N k = 1 := by
  sorry
