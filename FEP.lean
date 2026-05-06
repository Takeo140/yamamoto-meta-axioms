-- F-Theory: Formal Specification of Free Energy Principle (FEP)
-- Karl Friston's Theory formalized under F-Theory A1--A4
-- License: CC BY 4.0

import Mathlib.Data.Real.Basic

/-!
# Free Energy Principle (FEP) Specification

## F-Theory Mapping
- **A1 (Extremum)**: The system minimizes Variational Free Energy (VFE).
- **A2 (Topology)**: A Markov Blanket defines the boundary of the 'Self'.
- **A3 (Consistency)**: Internal generative models must align with environmental sensory data.
- **A4 (Hierarchy)**: Biological agency emerges through nested blankets.
-/

-- ============================================================
-- 1. States and Topology (A2: Markov Blanket)
-- ============================================================

/-- The Markov Blanket (b) consists of Sensory (s) and Active (a) states.
    It separates Internal states (μ) from External states (η). -/
structure MarkovBlanket where
  sensory : ℝ
  active  : ℝ

/-- The total state of a living system. -/
structure LivingSystem where
  eta    : ℝ  -- External causes (Hidden)
  blanket : MarkovBlanket
  mu     : ℝ  -- Internal model/representation

-- ============================================================
-- 2. Variational Free Energy (A1: Extremum)
-- ============================================================

/-- Variational Free Energy (F) is a functional of sensory and internal states.
    In F-Theory, this is the fundamental extremum function. -/
opaque VFE (s a mu : ℝ) : ℝ

/-- Surprise (Shannon Surprise) measures the improbability of sensory states. -/
opaque surprise (s : ℝ) : ℝ

/-- A1: Fundamental inequality: Free Energy is always an upper bound on Surprise.
    Minimizing F effectively minimizes the bound on surprise. -/
axiom free_energy_bounds_surprise (s a mu : ℝ) : 
  surprise s ≤ VFE s a mu

-- ============================================================
-- 3. Active Inference (A3: Consistency)
-- ============================================================

/-- Active Inference is the process of maintaining consistency between 
    the internal model and the environment via two pathways. -/
def isOptimized (sys : LivingSystem) : Prop :=
  -- 1. Perception: Updating internal states (mu)
  (∀ mu', VFE sys.blanket.sensory sys.blanket.active sys.mu ≤ 
          VFE sys.blanket.sensory sys.blanket.active mu') ∧
  -- 2. Action: Updating active states (a)
  (∀ a', VFE sys.blanket.sensory sys.blanket.active sys.mu ≤ 
         VFE sys.blanket.sensory a' sys.mu)

-- ============================================================
-- 4. Survival Theorem (The "Living" Condition)
-- ============================================================

/-- A system 'survives' if its surprise is kept within a homeostatic range. -/
def isSurviving (sys : LivingSystem) (threshold : ℝ) : Prop :=
  surprise sys.blanket.sensory < threshold

/-- Theorem: If a system successfully minimizes its VFE below a threshold,
    it is mathematically guaranteed to be in a state of survival (low surprise). -/
theorem survival_guarantee (sys : LivingSystem) (threshold : ℝ)
    (h_vfe : VFE sys.blanket.sensory sys.blanket.active sys.mu < threshold) :
    isSurviving sys threshold := by
  -- Proof: By F-Theory A1 (free_energy_bounds_surprise)
  have h_bound := free_energy_bounds_surprise sys.blanket.sensory sys.blanket.active sys.mu
  exact lt_of_le_of_lt h_bound h_vfe

-- ============================================================
-- 5. Nested Hierarchy (A4)
-- ============================================================

/-- A4: FEP scales from organelles to ecosystems. -/
inductive Scale : Type where
  | Organelle
  | Cell
  | Organ
  | Organism
  deriving DecidableEq, Ord

instance : LE Scale where le a b := (compare a b) != Ordering.gt
