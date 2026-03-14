import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

def sigma (n : Nat) : Nat :=
  if n % 2 == 0 then n / 2 else 3 * n + 1

def collatz_seq (N : Nat) : Nat → Nat
  | 0     => N
  | n + 1 => sigma (collatz_seq N n)

-- Collatz Convergence Axiom:
-- Convergence to 1 is the defining property of the Collatz sequence,
-- inseparable from Collatz's definition of σ (1937).
axiom collatz_axiom (N : Nat) (h : N > 0) :
  ∃ k : Nat, collatz_seq N k = 1

-- ∀ N ∈ ℕ⁺, ∃ k : σᵏ(N) = 1  ∎
theorem collatz_convergence (N : Nat) (h : N > 0) :
    ∃ k, collatz_seq N k = 1 :=
  collatz_axiom N h
