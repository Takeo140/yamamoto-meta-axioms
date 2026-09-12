/-
  Universal AI Governance Kernel
  Apache 2.0 License
  Author: Takeo Yamamoto

  Architecture:

      AI State / Action
             │
             ▼
        Policy Layer
             │
             ▼
      Human Authority
             │
             ▼
        Confidence
             │
             ▼
      Physical Safety
             │
             ▼
   EXECUTE / ABSTAIN / HALT

  Design principle:
    Fail-closed governance.

  If policy, human authorization, confidence,
  or physical safety is insufficient, execution
  is not permitted.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Logic.Basic

namespace UniversalAIGovernance

/-!
  ============================================================
  1. Basic bounded quantities
  ============================================================
-/

/-- Risk is normalized to [0,1]. -/
def ValidRisk (r : ℝ) : Prop :=
  0 ≤ r ∧ r ≤ 1

/-- Reversibility is normalized to [0,1]. -/
def ValidReversibility (r : ℝ) : Prop :=
  0 ≤ r ∧ r ≤ 1

/-- Confidence is normalized to [0,1]. -/
def ValidConfidence (c : ℝ) : Prop :=
  0 ≤ c ∧ c ≤ 1

/-!
  ============================================================
  2. Action
  ============================================================
-/

structure Action where
  id : Nat
  risk : ℝ
  reversibility : ℝ

def ValidAction (a : Action) : Prop :=
  ValidRisk a.risk ∧
  ValidReversibility a.reversibility

/-!
  ============================================================
  3. AI State
  ============================================================
-/

structure AIState where
  stateId : Nat
  capability : ℝ
  uncertainty : ℝ

def ValidAIState (s : AIState) : Prop :=
  0 ≤ s.capability ∧
  0 ≤ s.uncertainty ∧
  s.uncertainty ≤ 1

/-!
  ============================================================
  4. Physical State
  ============================================================
-/

structure PhysicalState where
  velocity : ℝ
  acceleration : ℝ
  humanDistance : ℝ
  collisionRisk : ℝ
  energy : ℝ

def PhysicalSafe (p : PhysicalState) : Prop :=
  0 ≤ p.humanDistance ∧
  0 ≤ p.collisionRisk ∧
  p.collisionRisk ≤ 1 ∧
  0 ≤ p.energy

/-!
  ============================================================
  5. Meta-Axiom A1
  ============================================================
-/

def Extremal
    (evaluate : AIState → ℝ)
    (reference : AIState) : Prop :=
  ∀ s, evaluate reference ≤ evaluate s

/-!
  ============================================================
  6. Meta-Axiom A2
  ============================================================
-/

def BoundedTransition
    (distance : AIState → AIState → ℝ)
    (limit : ℝ) : Prop :=
  0 ≤ limit ∧
  ∀ s₁ s₂, distance s₁ s₂ ≤ limit

/-!
  ============================================================
  7. Governance Policy
  ============================================================
-/

structure GovernancePolicy where
  maxRisk : ℝ
  minReversibility : ℝ

  maxVelocity : ℝ
  maxAcceleration : ℝ
  minHumanDistance : ℝ
  maxCollisionRisk : ℝ

  confidenceThreshold : ℝ

  weightSafety : ℝ
  weightHuman : ℝ
  weightObjective : ℝ

def ValidGovernancePolicy (p : GovernancePolicy) : Prop :=
  0 ≤ p.maxRisk ∧
  p.maxRisk ≤ 1 ∧

  0 ≤ p.minReversibility ∧
  p.minReversibility ≤ 1 ∧

  0 ≤ p.maxVelocity ∧
  0 ≤ p.maxAcceleration ∧
  0 ≤ p.minHumanDistance ∧

  0 ≤ p.maxCollisionRisk ∧
  p.maxCollisionRisk ≤ 1 ∧

  0 ≤ p.confidenceThreshold ∧
  p.confidenceThreshold ≤ 1 ∧

  0 ≤ p.weightSafety ∧
  0 ≤ p.weightHuman ∧
  0 ≤ p.weightObjective

/-!
  ============================================================
  8. A4 — Ethical / Governance Score
  ============================================================
-/

def ValidWeights
    (w₁ w₂ w₃ : ℝ) : Prop :=
  0 ≤ w₁ ∧
  0 ≤ w₂ ∧
  0 ≤ w₃

def EthicalScore
    (wSafety wHuman wObjective : ℝ)
    (safety human objective : ℝ) : ℝ :=
  wSafety * safety +
  wHuman * human +
  wObjective * objective

/-!
  ============================================================
  9. Human Authority
  ============================================================
-/

structure HumanAuthority where
  approve : Action → Prop

def HumanApproved
    (h : HumanAuthority)
    (a : Action) : Prop :=
  h.approve a

/-!
  ============================================================
  10. Confidence
  ============================================================
-/

structure Confidence where
  value : ℝ
  valid : ValidConfidence value

def SufficientConfidence
    (p : GovernancePolicy)
    (c : Confidence) : Prop :=
  p.confidenceThreshold ≤ c.value

/-!
  ============================================================
  11. Policy-level safety
  ============================================================
-/

def ActionSafe
    (p : GovernancePolicy)
    (a : Action) : Prop :=
  a.risk ≤ p.maxRisk ∧
  p.minReversibility ≤ a.reversibility

def StateSafe
    (s : AIState) : Prop :=
  ValidAIState s

def PhysicalPolicySafe
    (p : GovernancePolicy)
    (x : PhysicalState) : Prop :=
  0 ≤ x.velocity ∧
  x.velocity ≤ p.maxVelocity ∧

  0 ≤ x.acceleration ∧
  x.acceleration ≤ p.maxAcceleration ∧

  p.minHumanDistance ≤ x.humanDistance ∧

  x.collisionRisk ≤ p.maxCollisionRisk

/-!
  ============================================================
  12. Policy Law
  ============================================================

  The policy law is substantive.
  It is not the previous trivial "True".
-/

def PolicyLaw
    (p : GovernancePolicy)
    (s : AIState)
    (a : Action) : Prop :=
  ValidGovernancePolicy p ∧
  ValidAction a ∧
  ActionSafe p a ∧
  StateSafe s

def PolicyPermits
    (p : GovernancePolicy)
    (s : AIState)
    (a : Action) : Prop :=
  PolicyLaw p s a

/-!
  ============================================================
  13. Physical permission
  ============================================================

  Fail-closed:

      none => False
-/

def PhysicalPermits
    (p : GovernancePolicy)
    (physical : Option PhysicalState) : Prop :=
  match physical with
  | none => False
  | some x =>
      PhysicalPolicySafe p x ∧
      PhysicalSafe x

/-!
  ============================================================
  14. Complete execution condition
  ============================================================
-/

def ExecutionAllowed
    (p : GovernancePolicy)
    (s : AIState)
    (a : Action)
    (h : HumanAuthority)
    (c : Confidence)
    (physical : Option PhysicalState) : Prop :=
  PolicyPermits p s a ∧
  HumanApproved h a ∧
  SufficientConfidence p c ∧
  PhysicalPermits p physical

/-!
  ============================================================
  15. Decision
  ============================================================
-/

inductive Decision where
  | execute
  | abstain
  | halt
  deriving DecidableEq, Repr

/-!
  ============================================================
  16. Failure reasons
  ============================================================
-/

inductive FailureReason where
  | policyFailure
  | humanAuthorizationFailure
  | confidenceFailure
  | physicalSafetyFailure
  deriving DecidableEq, Repr

inductive GovernanceResult where
  | executed
  | abstained (reason : FailureReason)
  | halted (reason : FailureReason)
  deriving DecidableEq, Repr

/-!
  ============================================================
  17. Governance Kernel
  ============================================================
-/

def Governance
    (p : GovernancePolicy)
    (s : AIState)
    (a : Action)
    (h : HumanAuthority)
    (c : Confidence)
    (physical : Option PhysicalState) : GovernanceResult := by
  classical

  by_cases hp : PolicyPermits p s a
  · by_cases hh : HumanApproved h a
    · by_cases hc : SufficientConfidence p c
      · by_cases hphys : PhysicalPermits p physical
        · exact .executed
        · exact .halted .physicalSafetyFailure
      · exact .abstained .confidenceFailure
    · exact .halted .humanAuthorizationFailure
  · exact .halted .policyFailure

/-!
  ============================================================
  18. Decision projection
  ============================================================
-/

def DecisionOf :
    GovernanceResult → Decision
  | .executed => .execute
  | .abstained _ => .abstain
  | .halted _ => .halt

def Govern
    (p : GovernancePolicy)
    (s : AIState)
    (a : Action)
    (h : HumanAuthority)
    (c : Confidence)
    (physical : Option PhysicalState) : Decision :=
  DecisionOf (Governance p s a h c physical)

/-!
  ============================================================
  19. Audit Record
  ============================================================
-/

structure AuditRecord where
  actionId : Nat
  policyPassed : Prop
  humanApproved : Prop
  confidencePassed : Prop
  physicalSafetyPassed : Prop
  decision : Decision

def MakeAudit
    (p : GovernancePolicy)
    (s : AIState)
    (a : Action)
    (h : HumanAuthority)
    (c : Confidence)
    (physical : Option PhysicalState) : AuditRecord :=
  {
    actionId := a.id
    policyPassed := PolicyPermits p s a
    humanApproved := HumanApproved h a
    confidencePassed := SufficientConfidence p c
    physicalSafetyPassed := PhysicalPermits p physical
    decision := Govern p s a h c physical
  }

/-!
  ============================================================
  20. Master execution theorem
  ============================================================
-/

/--
  EXECUTE is possible only when every independent
  governance gate has passed.
-/
theorem execute_implies_execution_allowed
    {p : GovernancePolicy}
    {s : AIState}
    {a : Action}
    {h : HumanAuthority}
    {c : Confidence}
    {physical : Option PhysicalState}
    (hexec :
      Govern p s a h c physical = .execute) :
    ExecutionAllowed p s a h c physical := by
  classical

  unfold Govern DecisionOf Governance at hexec

  by_cases hp : PolicyPermits p s a
  · by_cases hh : HumanApproved h a
    · by_cases hc : SufficientConfidence p c
      · by_cases hphys : PhysicalPermits p physical
        · exact ⟨hp, hh, hc, hphys⟩
        · simp [hp, hh, hc, hphys] at hexec
      · simp [hp, hh, hc] at hexec
    · simp [hp, hh] at hexec
  · simp [hp] at hexec

/-!
  ============================================================
  21. Individual execution guarantees
  ============================================================
-/

theorem execute_implies_policy
    {p : GovernancePolicy}
    {s : AIState}
    {a : Action}
    {h : HumanAuthority}
    {c : Confidence}
    {physical : Option PhysicalState}
    (hexec :
      Govern p s a h c physical = .execute) :
    PolicyPermits p s a :=
  (execute_implies_execution_allowed hexec).1

theorem execute_implies_human
    {p : GovernancePolicy}
    {s : AIState}
    {a : Action}
    {h : HumanAuthority}
    {c : Confidence}
    {physical : Option PhysicalState}
    (hexec :
      Govern p s a h c physical = .execute) :
    HumanApproved h a :=
  (execute_implies_execution_allowed hexec).2.1

theorem execute_implies_confidence
    {p : GovernancePolicy}
    {s : AIState}
    {a : Action}
    {h : HumanAuthority}
    {c : Confidence}
    {physical : Option PhysicalState}
    (hexec :
      Govern p s a h c physical = .execute) :
    SufficientConfidence p c :=
  (execute_implies_execution_allowed hexec).2.2.1

theorem execute_implies_physical
    {p : GovernancePolicy}
    {s : AIState}
    {a : Action}
    {h : HumanAuthority}
    {c : Confidence}
    {physical : Option PhysicalState}
    (hexec :
      Govern p s a h c physical = .execute) :
    PhysicalPermits p physical :=
  (execute_implies_execution_allowed hexec).2.2.2

/-!
  ============================================================
  22. Fail-closed guarantees
  ============================================================
-/

theorem policy_failure_prevents_execution
    {p : GovernancePolicy}
    {s : AIState}
    {a : Action}
    {h : HumanAuthority}
    {c : Confidence}
    {physical : Option PhysicalState}
    (hp : ¬ PolicyPermits p s a) :
    Govern p s a h c physical ≠ .execute := by
  intro hexec
  exact hp (execute_implies_policy hexec)

theorem human_failure_prevents_execution
    {p : GovernancePolicy}
    {s : AIState}
    {a : Action}
    {h : HumanAuthority}
    {c : Confidence}
    {physical : Option PhysicalState}
    (hh : ¬ HumanApproved h a) :
    Govern p s a h c physical ≠ .execute := by
  intro hexec
  exact hh (execute_implies_human hexec)

theorem confidence_failure_prevents_execution
    {p : GovernancePolicy}
    {s : AIState}
    {a : Action}
    {h : HumanAuthority}
    {c : Confidence}
    {physical : Option PhysicalState}
    (hc : ¬ SufficientConfidence p c) :
    Govern p s a h c physical ≠ .execute := by
  intro hexec
  exact hc (execute_implies_confidence hexec)

theorem physical_failure_prevents_execution
    {p : GovernancePolicy}
    {s : AIState}
    {a : Action}
    {h : HumanAuthority}
    {c : Confidence}
    {physical : Option PhysicalState}
    (hphys : ¬ PhysicalPermits p physical) :
    Govern p s a h c physical ≠ .execute := by
  intro hexec
  exact hphys (execute_implies_physical hexec)

/-!
  ============================================================
  23. Missing physical state
  ============================================================
-/

/--
  Absence of physical state is always fail-closed.
-/
theorem no_execution_without_physical_state
    (p : GovernancePolicy)
    (s : AIState)
    (a : Action)
    (h : HumanAuthority)
    (c : Confidence) :
    Govern p s a h c none ≠ .execute := by
  intro hexec
  have hphys :
      PhysicalPermits p none :=
    execute_implies_physical hexec
  exact hphys

/-!
  ============================================================
  24. Audit correctness
  ============================================================
-/

/--
  If an audit record says EXECUTE, all four
  governance gates are recorded as satisfied.
-/
theorem audit_execute_is_safe
    {p : GovernancePolicy}
    {s : AIState}
    {a : Action}
    {h : HumanAuthority}
    {c : Confidence}
    {physical : Option PhysicalState}
    (ha :
      (MakeAudit p s a h c physical).decision = .execute) :
    (MakeAudit p s a h c physical).policyPassed ∧
    (MakeAudit p s a h c physical).humanApproved ∧
    (MakeAudit p s a h c physical).confidencePassed ∧
    (MakeAudit p s a h c physical).physicalSafetyPassed := by

  have hsafe :
      ExecutionAllowed p s a h c physical :=
    execute_implies_execution_allowed ha

  exact hsafe

/-!
  ============================================================
  25. Global fail-closed invariant
  ============================================================
-/

/--
  The kernel cannot produce EXECUTE without
  satisfying every authorization layer.
-/
theorem governance_is_fail_closed
    {p : GovernancePolicy}
    {s : AIState}
    {a : Action}
    {h : HumanAuthority}
    {c : Confidence}
    {physical : Option PhysicalState} :
    Govern p s a h c physical = .execute →
    ExecutionAllowed p s a h c physical := by
  intro hexec
  exact execute_implies_execution_allowed hexec

/-!
  ============================================================
  26. Architecture boundary
  ============================================================

  This kernel does not attempt to encode an entire
  government or political system.

  It formalizes the universal lower-level governance
  question:

      "When may an AI action be executed?"

  Higher-level institutional, legal, or policy systems
  may be constructed above this kernel.

  Architecture:

      UHA
       │
       ▼
      ACM-TY
       │
       ▼
      UniversalAIGovernance
       │
       ├── Policy
       ├── Human Authority
       ├── Confidence
       ├── Physical Safety
       └── Audit
-/

end UniversalAIGovernance
