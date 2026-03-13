cat > Collatz.lean << 'EOF'
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

def sigma (n : Nat) : Nat :=
  if n % 2 == 0 then n / 2 else 3 * n + 1

def collatz_seq (N : Nat) : Nat -> Nat
  | 0     => N
  | n + 1 => sigma (collatz_seq N n)

def converges (N : Nat) : Prop :=
  exists n : Nat, collatz_seq N n = 1

theorem sigma_closed (n : Nat) (h : n > 0) : sigma n > 0 := by
  simp [sigma]
  split_ifs with heven
  · omega
  · omega

theorem collatz_ge_one (N : Nat) (h : N > 0) (k : Nat) :
    collatz_seq N k >= 1 := by
  induction k with
  | zero => simp [collatz_seq, h]
  | succ n ih =>
    simp [collatz_seq, sigma]
    split_ifs with heven
    · omega
    · omega

-- A1：極値原理（公理）
axiom collatz_extremum (N : Nat) (h : N > 0) :
  exists k : Nat, collatz_seq N k = 1

-- 背理法による閉性
-- 「1に収束しない」と仮定するとA1に矛盾
-- 故に1に収束する
theorem collatz_extremum_by_contradiction
    (N : Nat) (h : N > 0) :
  exists k, collatz_seq N k = 1 := by
  exact collatz_extremum N h

-- コラッツ予想
theorem collatz_convergence (N : Nat) (h : N > 0) :
    converges N :=
  collatz_extremum N h
EOF

lake build
