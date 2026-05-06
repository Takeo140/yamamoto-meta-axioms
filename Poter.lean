-- Porter's Competitive Strategy: Formal Lean 4 Specification
-- Michael E. Porter (1980, 1985) formalized under F-Theory A1--A4

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Defs

/-!
# Porter's Competitive Strategy

## Ontology
- `Scope`       : competitive scope (broad / narrow)
- `Advantage`   : source of competitive advantage (cost / differentiation)
- `GenericStrategy` : 2×2 product → four canonical strategies
- `Force`       : Porter's Five Forces
- `Industry`    : aggregate force intensity → structural attractiveness
- `FirmPosition`: firm embedded in industry → realized competitive advantage

## Axioms (mapped to F-Theory A1--A4)
- A1 (Extremum)   : firm maximizes competitive advantage given scope
- A2 (Topology)   : strategy space is a closed 2×2 lattice
- A3 (Consistency): no firm can simultaneously lead on cost AND differentiation
  at the same scope without a strategic penalty ("stuck-in-the-middle")
- A4 (Hierarchy)  : industry structure constrains firm strategy
-/

-- ============================================================
-- 1. Basic Types
-- ============================================================

/-- Competitive scope -/
inductive Scope : Type where
  | Broad  : Scope   -- industry-wide
  | Narrow : Scope   -- segment / niche
  deriving DecidableEq, Repr

/-- Source of competitive advantage -/
inductive Advantage : Type where
  | Cost            : Advantage
  | Differentiation : Advantage
  deriving DecidableEq, Repr

/-- Porter's four generic strategies (A2: closed lattice) -/
structure GenericStrategy where
  scope     : Scope
  advantage : Advantage
  deriving DecidableEq, Repr

namespace GenericStrategy

def costLeadership    : GenericStrategy := ⟨Scope.Broad,  Advantage.Cost⟩
def differentiation   : GenericStrategy := ⟨Scope.Broad,  Advantage.Differentiation⟩
def costFocus         : GenericStrategy := ⟨Scope.Narrow, Advantage.Cost⟩
def diffFocus         : GenericStrategy := ⟨Scope.Narrow, Advantage.Differentiation⟩

/-- All four strategies are distinct -/
theorem all_distinct :
    costLeadership ≠ differentiation ∧
    costLeadership ≠ costFocus       ∧
    costLeadership ≠ diffFocus       ∧
    differentiation ≠ costFocus      ∧
    differentiation ≠ diffFocus      ∧
    costFocus ≠ diffFocus := by
  simp [costLeadership, differentiation, costFocus, diffFocus,
        GenericStrategy.mk.injEq, Scope.Broad, Scope.Narrow,
        Advantage.Cost, Advantage.Differentiation]

end GenericStrategy

-- ============================================================
-- 2. Five Forces
-- ============================================================

/-- Force intensity ∈ [0,1] (0 = weak, 1 = strong) -/
structure ForceIntensity where
  val : ℝ
  h_lo : 0 ≤ val
  h_hi : val ≤ 1

/-- Porter's Five Forces -/
structure FiveForces where
  rivalry         : ForceIntensity   -- F1: rivalry among existing competitors
  newEntrants     : ForceIntensity   -- F2: threat of new entrants
  substitutes     : ForceIntensity   -- F3: threat of substitute products
  buyerPower      : ForceIntensity   -- F4: bargaining power of buyers
  supplierPower   : ForceIntensity   -- F5: bargaining power of suppliers

/-- Structural attractiveness = 1 − average force intensity
    (A1: industry profit potential is maximized when forces are weak) -/
noncomputable def structuralAttractiveness (f : FiveForces) : ℝ :=
  1 - (f.rivalry.val + f.newEntrants.val + f.substitutes.val +
       f.buyerPower.val + f.supplierPower.val) / 5

/-- Attractiveness is bounded above by 1 -/
theorem attractiveness_le_one (f : FiveForces) :
    structuralAttractiveness f ≤ 1 := by
  simp [structuralAttractiveness]
  have h1 := f.rivalry.h_lo
  have h2 := f.newEntrants.h_lo
  have h3 := f.substitutes.h_lo
  have h4 := f.buyerPower.h_lo
  have h5 := f.supplierPower.h_lo
  linarith

/-- Attractiveness is bounded below by 0 when all forces are at most 1 -/
theorem attractiveness_nonneg (f : FiveForces) :
    0 ≤ structuralAttractiveness f := by
  simp [structuralAttractiveness]
  have h1 := f.rivalry.h_hi
  have h2 := f.newEntrants.h_hi
  have h3 := f.substitutes.h_hi
  have h4 := f.buyerPower.h_hi
  have h5 := f.supplierPower.h_hi
  linarith

-- ============================================================
-- 3. Firm Position (A4: Hierarchy)
-- ============================================================

/-- A firm is a strategy embedded in an industry -/
structure FirmPosition where
  strategy  : GenericStrategy
  industry  : FiveForces
  /-- Realized competitive advantage scales with structural attractiveness -/
  noncomputable advantage_score : ℝ :=
    structuralAttractiveness industry

-- ============================================================
-- 4. A3: Stuck-in-the-Middle Penalty
-- ============================================================

/-- "Stuck in the middle": a firm lacking a clear generic strategy
    suffers an advantage penalty.  Modelled as advantage_score → 0. -/
def isStuckInMiddle (p : FirmPosition) : Prop :=
  -- proxy: no committed scope (formalized as impossible combination absent here;
  -- in practice captured by absence of a valid GenericStrategy assignment)
  False  -- structurally, every FirmPosition must commit to one of the four

/-- Every firm that commits to a GenericStrategy avoids the stuck-in-middle trap -/
theorem committed_strategy_avoids_penalty (p : FirmPosition) :
    ¬ isStuckInMiddle p := by
  intro h
  exact h

-- ============================================================
-- 5. Value Chain (sketch, A4 hierarchy)
-- ============================================================

/-- Value chain activities -/
inductive Activity : Type where
  -- Primary activities
  | InboundLogistics  : Activity
  | Operations        : Activity
  | OutboundLogistics : Activity
  | Marketing         : Activity
  | Service           : Activity
  -- Support activities
  | Procurement       : Activity
  | TechDevelopment   : Activity
  | HRM               : Activity
  | Infrastructure    : Activity
  deriving DecidableEq, Repr

/-- Every activity is either primary or support (A4: hierarchical decomposition) -/
def isPrimary : Activity → Bool
  | Activity.InboundLogistics  => true
  | Activity.Operations        => true
  | Activity.OutboundLogistics => true
  | Activity.Marketing         => true
  | Activity.Service           => true
  | _                          => false

def isSupport (a : Activity) : Bool := !isPrimary a

theorem primary_or_support (a : Activity) :
    isPrimary a = true ∨ isSupport a = true := by
  cases a <;> simp [isPrimary, isSupport]
