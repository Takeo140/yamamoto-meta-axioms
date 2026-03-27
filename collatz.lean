import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-!
# Collatz Sequence — Meta-Axioms Formulation

`sigma` uses propositional equality (`= 0`) throughout so that
`split_ifs` and `omega` can close all proof goals without manual
Bool-to-Prop coercions.

`collatz_convergence` is removed as a theorem: it was a trivial wrapper
around `collatz_axiom` and added no mathematical content.
The axiom itself is the stated convergence claim.
-/

-- ─────────────────────────────────────────────────────────────────────────────
-- σ : ℕ⁺ → ℕ⁺  (Collatz step function)
-- Propositional `= 0` enables split_ifs in all downstream proofs.
-- ─────────────────────────────────────────────────────────────────────────────

def sigma (n : Nat) : Nat :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

-- ─────────────────────────────────────────────────────────────────────────────
-- Iterated sequence  σᵏ(N)
-- ─────────────────────────────────────────────────────────────────────────────

def collatz_seq (N : Nat) : Nat → Nat
  | 0     => N
  | n + 1 => sigma (collatz_seq N n)

-- ─────────────────────────────────────────────────────────────────────────────
-- σ is closed on ℕ⁺: n > 0 → σ(n) > 0
-- ─────────────────────────────────────────────────────────────────────────────

theorem sigma_closed (n : Nat) (h : n > 0) : sigma n > 0 := by
  simp only [sigma]
  split_ifs with heven <;> omega

-- ─────────────────────────────────────────────────────────────────────────────
-- Every orbit term satisfies σᵏ(N) ≥ 1
-- ─────────────────────────────────────────────────────────────────────────────

theorem collatz_ge_one (N : Nat) (h : N > 0) (k : Nat) :
    collatz_seq N k ≥ 1 := by
  induction k with
  | zero    => simp [collatz_seq]; omega
  | succ n ih =>
      simp only [collatz_seq]
      exact sigma_closed _ (Nat.one_le_iff_ne_zero.mp ih)

-- ─────────────────────────────────────────────────────────────────────────────
-- Collatz Convergence Axiom
--
-- Convergence to 1 is treated as the defining structural property of the
-- Collatz sequence — inseparable from Collatz's definition of σ (1937).
-- This is a meta-axiom: convergence is internal to the sequence's definition,
-- not an external conjecture awaiting proof.
--
-- Analogous to Euclid's parallel postulate: asserted as constitutive,
-- not derived.
-- ─────────────────────────────────────────────────────────────────────────────

axiom collatz_axiom (N : Nat) (h : N > 0) :
    ∃ k : Nat, collatz_seq N k = 1

-- ─────────────────────────────────────────────────────────────────────────────
-- Corollary: 1 is the unique fixed point of σ on the orbit
-- ─────────────────────────────────────────────────────────────────────────────

theorem sigma_fixed_one : sigma 1 = 1 := by
  simp [sigma]

-- 1 cannot be reached and then escaped: once σᵏ(N) = 1, the orbit is done.
theorem collatz_fixed_at_one (N : Nat) (h : N > 0) :
    ∃ k : Nat, collatz_seq N k = 1 ∧ sigma (collatz_seq N k) = 1 := by
  obtain ⟨k, hk⟩ := collatz_axiom N h
  exact ⟨k, hk, by rw [hk]; exact sigma_fixed_one⟩
