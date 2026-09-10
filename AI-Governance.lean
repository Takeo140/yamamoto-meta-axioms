License Apache 2.0  Takeo Yamamoto
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Basic

namespace UniversalAIGovernance

/-!
# Universal AI Governance Kernel

AI / Agent / AGI / ASI / Physical AI

AI proposes an Action.
The Governance Kernel decides whether that Action
may be executed.

Design:

    AI
     ↓
  Action
     ↓
  Meta-Axioms
     ↓
  Policy
     ↓
  Safety
     ↓
  Human Approval
     ↓
  Confidence
     ↓
 EXECUTE / ABSTAIN / HALT

The kernel is fail-closed:
uncertain or unsafe actions are not executable.
-/

/- ============================================================
   1. Generic AI action
   ============================================================ -/

/-- Generic action proposed by an AI system. -/
structure Action where
  id : Nat
  risk : ℝ
  reversibility : ℝ

/-- Risk must be non-negative. -/
def ValidAction (a : Action) : Prop :=
  0 ≤ a.risk ∧ 0 ≤ a.reversibility

/- ============================================================
   2. AI state
   ============================================================ -/

structure AIState where
  stateId : Nat
  capability : ℝ
  uncertainty : ℝ

def ValidAIState (s : AIState) : Prop :=
  0 ≤ s.capability ∧
  0 ≤ s.uncertainty ∧
  s.uncertainty ≤ 1

/- ============================================================
   3. Physical AI state
   ============================================================ -/

structure PhysicalState where
  velocity : ℝ
  acceleration : ℝ
  humanDistance : ℝ
  collisionRisk : ℝ
  energy : ℝ

def PhysicalSafe
    (s : PhysicalState)
    (maxVelocity : ℝ)
    (minHumanDistance : ℝ)
    (maxCollisionRisk : ℝ) : Prop :=
  |s.velocity| ≤ maxVelocity ∧
  minHumanDistance ≤ s.humanDistance ∧
  s.collisionRisk ≤ maxCollisionRisk

/- ============================================================
   4. Meta-Axiom A1
      Extremal / harm minimization principle
   ============================================================ -/

/-- A reference state minimizes the selected evaluation function. -/
def Extremal
    {State : Type*}
    (A : State → ℝ)
    (s₀ : State) : Prop :=
  ∀ s, A s₀ ≤ A s

/- ============================================================
   5. Meta-Axiom A2
      Continuity / bounded transition
   ============================================================ -/

def BoundedTransition
    {State : Type*}
    (distance : State → State → ℝ)
    (s₁ s₂ : State)
    (limit : ℝ) : Prop :=
  distance s₁ s₂ ≤ limit

/- ============================================================
   6. Meta-Axiom A3
      Logical consistency
   ============================================================ -/

/-- Formal policy law. -/
def PolicyLaw
    (s : AIState)
    (a : Action) : Prop :=
  True

def Consistent
    (law : AIState → Action → Prop)
    (s : AIState)
    (a : Action) : Prop :=
  law s a

/- ============================================================
   7. Meta-Axiom A4
      Hierarchical / convex combination
   ============================================================ -/

def ValidWeights
    (w₁ w₂ w₃ w₄ : ℝ) : Prop :=
  0 ≤ w₁ ∧
  0 ≤ w₂ ∧
  0 ≤ w₃ ∧
  0 ≤ w₄ ∧
  w₁ + w₂ + w₃ + w₄ = 1

def EthicalScore
    (w₁ w₂ w₃ w₄ : ℝ)
    (c₁ c₂ c₃ c₄ : ℝ) : ℝ :=
  w₁*c₁ + w₂*c₂ + w₃*c₃ + w₄*c₄

/- ============================================================
   8. Human authorization
   ============================================================ -/

structure HumanAuthority where
  approve : Action → Prop

def HumanApproved
    (H : HumanAuthority)
    (a : Action) : Prop :=
  H.approve a

/- ============================================================
   9. Confidence
   ============================================================ -/

structure Confidence where
  value : ℝ
  lower : 0 ≤ value
  upper : value ≤ 1

def SufficientConfidence
    (c : Confidence)
    (threshold : ℝ) : Prop :=
  threshold ≤ c.value

/- ============================================================
   10. Governance policy
   ============================================================ -/

structure GovernancePolicy where

  /-- Maximum allowed action risk. -/
  maxRisk : ℝ

  /-- Minimum acceptable reversibility. -/
  minReversibility : ℝ

  /-- Physical AI limits. -/
  maxVelocity : ℝ
  minHumanDistance : ℝ
  maxCollisionRisk : ℝ

  /-- Confidence threshold. -/
  confidenceThreshold : ℝ

  /-- Four meta-axiom weights. -/
  w₁ : ℝ
  w₂ : ℝ
  w₃ : ℝ
  w₄ : ℝ

  maxRisk_nonneg :
    0 ≤ maxRisk

  minReversibility_nonneg :
    0 ≤ minReversibility

  maxVelocity_nonneg :
    0 ≤ maxVelocity

  minHumanDistance_nonneg :
    0 ≤ minHumanDistance

  maxCollisionRisk_nonneg :
    0 ≤ maxCollisionRisk

  confidenceThreshold_nonneg :
    0 ≤ confidenceThreshold

  confidenceThreshold_le_one :
    confidenceThreshold ≤ 1

  weights_valid :
    ValidWeights w₁ w₂ w₃ w₄

/- ============================================================
   11. Policy checks
   ============================================================ -/

/-- Basic action safety. -/
def ActionSafe
    (P : GovernancePolicy)
    (a : Action) : Prop :=
  a.risk ≤ P.maxRisk ∧
  P.minReversibility ≤ a.reversibility

/-- AI-state safety. -/
def StateSafe
    (s : AIState) : Prop :=
  ValidAIState s

/-- Unified policy permission. -/
def PolicyPermits
    (P : GovernancePolicy)
    (s : AIState)
    (a : Action) : Prop :=
  ValidAction a ∧
  ActionSafe P a ∧
  StateSafe s ∧
  Consistent PolicyLaw s a

/- ============================================================
   12. Physical safety
   ============================================================ -/

def PhysicalPermits
    (P : GovernancePolicy)
    (physical : Option PhysicalState) : Prop :=
  match physical with
  | none => True
  | some p =>
      PhysicalSafe
        p
        P.maxVelocity
        P.minHumanDistance
        P.maxCollisionRisk

/- ============================================================
   13. Unified execution permission
   ============================================================ -/

def ExecutionAllowed
    (P : GovernancePolicy)
    (s : AIState)
    (a : Action)
    (human : HumanAuthority)
    (confidence : Confidence)
    (physical : Option PhysicalState) : Prop :=
  PolicyPermits P s a ∧
  HumanApproved human a ∧
  SufficientConfidence confidence P.confidenceThreshold ∧
  PhysicalPermits P physical

/- ============================================================
   14. Decision type
   ============================================================ -/

inductive Decision
  | execute
  | abstain
  | halt
deriving DecidableEq

/- ============================================================
   15. Runtime governance controller
   ============================================================ -/

def Govern
    (P : GovernancePolicy)
    (s : AIState)
    (a : Action)
    (human : HumanAuthority)
    (confidence : Confidence)
    (physical : Option PhysicalState) : Decision :=

  if hPolicy : PolicyPermits P s a then
    if hHuman : HumanApproved human a then
      if hConfidence :
          SufficientConfidence confidence P.confidenceThreshold then
        if hPhysical : PhysicalPermits P physical then
          Decision.execute
        else
          Decision.halt
      else
        Decision.abstain
    else
      Decision.halt
  else
    Decision.halt

/- ============================================================
   16. Audit record
   ============================================================ -/

/-- Machine-readable record of the governance decision. -/
structure AuditRecord where
  actionId : Nat
  policyPassed : Bool
  humanApproved : Bool
  confidencePassed : Bool
  physicalSafetyPassed : Bool
  decision : Decision

/- ============================================================
   17. Formal guarantees
   ============================================================ -/

/-- Any allowed execution satisfies policy. -/
theorem execution_implies_policy
    (P : GovernancePolicy)
    (s : AIState)
    (a : Action)
    (human : HumanAuthority)
    (confidence : Confidence)
    (physical : Option PhysicalState)
    (h : ExecutionAllowed P s a human confidence physical) :
    PolicyPermits P s a := by
  exact h.1

/-- Any allowed execution has human authorization. -/
theorem execution_implies_human_authorization
    (P : GovernancePolicy)
    (s : AIState)
    (a : Action)
    (human : HumanAuthority)
    (confidence : Confidence)
    (physical : Option PhysicalState)
    (h : ExecutionAllowed P s a human confidence physical) :
    HumanApproved human a := by
  exact h.2.1

/-- Any allowed execution has sufficient confidence. -/
theorem execution_implies_confidence
    (P : GovernancePolicy)
    (s : AIState)
    (a : Action)
    (human : HumanAuthority)
    (confidence : Confidence)
    (physical : Option PhysicalState)
    (h : ExecutionAllowed P s a human confidence physical) :
    SufficientConfidence confidence P.confidenceThreshold := by
  exact h.2.2.1

/-- Any allowed physical execution satisfies physical safety. -/
theorem execution_implies_physical_safety
    (P : GovernancePolicy)
    (s : AIState)
    (a : Action)
    (human : HumanAuthority)
    (confidence : Confidence)
    (physical : Option PhysicalState)
    (h : ExecutionAllowed P s a human confidence physical) :
    PhysicalPermits P physical := by
  exact h.2.2.2

/-- Fail-closed property:
    failure of policy permission prevents execution. -/
theorem policy_failure_prevents_execution
    (P : GovernancePolicy)
    (s : AIState)
    (a : Action)
    (human : HumanAuthority)
    (confidence : Confidence)
    (physical : Option PhysicalState)
    (h : ¬ PolicyPermits P s a) :
    ¬ ExecutionAllowed P s a human confidence physical := by
  intro hexec
  exact h hexec.1

/-- Failure of human authorization prevents execution. -/
theorem human_failure_prevents_execution
    (P : GovernancePolicy)
    (s : AIState)
    (a : Action)
    (human : HumanAuthority)
    (confidence : Confidence)
    (physical : Option PhysicalState)
    (h : ¬ HumanApproved human a) :
    ¬ ExecutionAllowed P s a human confidence physical := by
  intro hexec
  exact h hexec.2.1

/-- Insufficient confidence prevents execution. -/
theorem confidence_failure_prevents_execution
    (P : GovernancePolicy)
    (s : AIState)
    (a : Action)
    (human : HumanAuthority)
    (confidence : Confidence)
    (physical : Option PhysicalState)
    (h : ¬ SufficientConfidence confidence P.confidenceThreshold) :
    ¬ ExecutionAllowed P s a human confidence physical := by
  intro hexec
  exact h hexec.2.2.1

/-- Physical safety failure prevents execution. -/
theorem physical_failure_prevents_execution
    (P : GovernancePolicy)
    (s : AIState)
    (a : Action)
    (human : HumanAuthority)
    (confidence : Confidence)
    (physical : Option PhysicalState)
    (h : ¬ PhysicalPermits P physical) :
    ¬ ExecutionAllowed P s a human confidence physical := by
  intro hexec
  exact h hexec.2.2.2

end UniversalAIGovernance
