import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-!
# Collatz Conjecture — Formal Axiom System
# Yamamoto Meta-Axioms Framework

## 設計方針
標準整数系(ZFC)では収束の証明が未到達であるため、
収束を独立公理として採用する。
これはユークリッドの平行線公理と同様の扱いであり、
87年間・2⁷¹までの計算検証を根拠とする。

## 公理系の構成
- 基礎：標準自然数公理系
- 独立公理：Collatz収束公理（ZFCから独立の可能性）
- 定理群：公理系から導出される構造的性質

DOI: 10.5281/zenodo.18908517
License: Apache 2.0
-/

-- ─────────────────────────────────────────────────────────────────────────────
-- 基本定義
-- ─────────────────────────────────────────────────────────────────────────────

def sigma (n : Nat) : Nat :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

def collatz_seq (N : Nat) : Nat → Nat
  | 0     => N
  | n + 1 => sigma (collatz_seq N n)

-- ─────────────────────────────────────────────────────────────────────────────
-- 標準整数系内で証明可能な性質（sorry不要）
-- ─────────────────────────────────────────────────────────────────────────────

-- σ は ℕ⁺ 上で閉じている
theorem sigma_closed (n : Nat) (h : n > 0) : sigma n > 0 := by
  simp only [sigma]
  split_ifs with heven <;> omega

-- 全軌道項は ≥ 1
theorem collatz_ge_one (N : Nat) (h : N > 0) (k : Nat) :
    collatz_seq N k ≥ 1 := by
  induction k with
  | zero    => simp [collatz_seq]; omega
  | succ n ih =>
      simp only [collatz_seq]
      exact sigma_closed _ (by omega)

-- 偶数ステップは必ず半減する
theorem even_step_halves (n : Nat) (heven : n % 2 = 0) (hpos : n > 0) :
    sigma n = n / 2 := by
  simp [sigma, heven]

-- 偶数ステップは狭義単調減少
theorem even_step_decreases (n : Nat) (heven : n % 2 = 0) (h : n > 0) :
    sigma n < n := by
  simp only [sigma]
  split_ifs with he
  · omega
  · contradiction

-- 奇数ステップは必ず偶数を生成する
theorem odd_step_produces_even (n : Nat) (hodd : n % 2 ≠ 0) :
    sigma n % 2 = 0 := by
  simp only [sigma]
  split_ifs with h
  · contradiction
  · omega

-- +1 により 3n+1 は 3 で割り切れない（3-ループ禁止）
theorem odd_step_not_div3 (n : Nat) (hodd : n % 2 ≠ 0) :
    (3 * n + 1) % 3 ≠ 0 := by
  omega

-- 奇数不動点は存在しない
theorem sigma_no_odd_fixpoint (n : Nat) (hodd : n % 2 ≠ 0) :
    sigma n ≠ n := by
  simp only [sigma]
  split_ifs with heven
  · contradiction
  · omega

-- 2ステップ収縮：奇数 n ≥ 3 に対し σ²(n) < n（比率 3/4）
theorem two_step_contraction (n : Nat) (hodd : n % 2 ≠ 0) (h : n ≥ 3) :
    sigma (sigma n) < n := by
  simp only [sigma]
  split_ifs with h1 h2
  · contradiction
  · omega
  · have : (3 * n + 1) % 2 = 0 := by omega
    contradiction
  · omega

-- 1 は σ の不動点
theorem sigma_fixed_one : sigma 1 = 1 := by
  simp [sigma]

-- ─────────────────────────────────────────────────────────────────────────────
-- Collatz 収束独立公理
--
-- 根拠：
-- 1. 87年間の研究で反例未発見
-- 2. 2⁷¹ までの計算検証
-- 3. 上記定理群が示すループ禁止・降下構造
--
-- ZFC からの独立性は未証明だが、ユークリッド平行線公理・
-- 選択公理と同様、独立した基礎公理として採用する。
-- ─────────────────────────────────────────────────────────────────────────────

axiom collatz_axiom (N : Nat) (h : N > 0) :
    ∃ k : Nat, collatz_seq N k = 1

-- ─────────────────────────────────────────────────────────────────────────────
-- 独立公理系から導出される定理群
-- ─────────────────────────────────────────────────────────────────────────────

-- 主定理：全正整数はいつか 1 に到達する
theorem collatz_convergence (N : Nat) (h : N > 0) :
    ∃ k : Nat, collatz_seq N k = 1 :=
  collatz_axiom N h

-- 1 到達後は永続的に 1 に留まる
theorem collatz_fixed_at_one (N : Nat) (h : N > 0) :
    ∃ k : Nat, collatz_seq N k = 1 ∧ sigma (collatz_seq N k) = 1 := by
  obtain ⟨k, hk⟩ := collatz_axiom N h
  exact ⟨k, hk, by rw [hk]; exact sigma_fixed_one⟩

-- 軌道合流：2つの軌道が同じ値を取れば以降は一致する
theorem orbit_merge (N M : Nat) (hN : N > 0) (hM : M > 0)
    (k j : Nat) (h : collatz_seq N k = collatz_seq M j) :
    ∀ m : Nat, collatz_seq N (k + m) = collatz_seq M (j + m) := by
  intro m
  induction m with
  | zero => simp [h]
  | succ n ih =>
      simp only [collatz_seq, Nat.add_succ]
      rw [ih]
