License Apache 2.0  Takeo Yamamoto
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Basic
import Mathlib.Logic.Basic

namespace FTheory

/-!
# F-Theory Physical AI Ethics Kernel
#
# A proof-oriented ethical constraint layer for Physical AI.
#
# Architecture:
#
#   Physical World
#        ↓
#   PhysicalState
#        ↓
#   Obverse ↔ Reverse
#        ↓
#   Ethical Law
#        ↓
#   Action Evaluation
#        ↓
#   EXECUTE / ABSTAIN / HALT
#
# The kernel is independent of a particular robot or actuator.
# Action is therefore parameterized as a type.
#
# Core principles:
#
# E1: Physical-state representation
# E2: Obverse-Reverse consistency
# E3: Harm minimization
# E4: Hard physical safety constraints
# E5: Action-level ethical constraints
# E6: Human oversight
# E7: Confidence / abstention
# E8: Formal execution gate
# E9: HALT fallback
-/

/- ============================================================
   1. Physical State
   ============================================================ -/

/--
Abstract physical state of a Physical AI system.

X represents the physical/environmental state space.
-/
structure PhysicalState (X : Type*) where
  position       : X
  velocity       : ℝ
  acceleration   : ℝ
  humanDistance  : ℝ
  collisionRisk  : ℝ
  energy         : ℝ


/- ============================================================
   2. Obverse / Reverse
   ============================================================ -/

/--
Obverse = physical/material aspect.
-/
structure Obverse (X : Type*) where
  state : PhysicalState X


/--
Reverse = formal law / ethical constraint.

The central law now acts on BOTH the physical state
and the proposed physical action.

This makes the kernel action-aware.
-/
structure Reverse
    (X : Type*)
    (A : Type*) where

  /--
  Fundamental ethical law.

  `Law S a` means that action `a` is ethically permitted
  in physical state `S`.
  -/
  Law : PhysicalState X → A → Prop

  /-- Maximum permitted velocity. -/
  maxVelocity : ℝ

  /-- Minimum permitted human distance. -/
  minHumanDistance : ℝ

  /-- Maximum permitted collision risk. -/
  maxCollisionRisk : ℝ

  positiveVelocityLimit :
    0 < maxVelocity

  nonnegativeDistanceLimit :
    0 ≤ minHumanDistance

  collisionRiskLower :
    0 ≤ maxCollisionRisk

  collisionRiskUpper :
    maxCollisionRisk ≤ 1


/- ============================================================
   3. Coupled F-Theory State
   ============================================================ -/

/--
Psi couples physical reality with its formal law.

Obverse = what physically exists.
Reverse = what is formally permitted.
-/
structure Psi
    (X : Type*)
    (A : Type*) where

  phys : Obverse X
  math : Reverse X A


/- ============================================================
   4. Physical Safety Constraints
   ============================================================ -/

/-- Velocity constraint. -/
def VelocitySafe
    {X : Type*}
    {A : Type*}
    (R : Reverse X A)
    (S : PhysicalState X) : Prop :=
  |S.velocity| ≤ R.maxVelocity


/-- Human-distance constraint. -/
def HumanDistanceSafe
    {X : Type*}
    {A : Type*}
    (R : Reverse X A)
    (S : PhysicalState X) : Prop :=
  R.minHumanDistance ≤ S.humanDistance


/-- Collision-risk constraint. -/
def CollisionRiskSafe
    {X : Type*}
    {A : Type*}
    (R : Reverse X A)
    (S : PhysicalState X) : Prop :=
  S.collisionRisk ≤ R.maxCollisionRisk


/--
Complete hard physical safety condition.

These constraints are NOT weighted preferences.
They are hard constraints.
-/
def PhysicallySafe
    {X : Type*}
    {A : Type*}
    (R : Reverse X A)
    (S : PhysicalState X) : Prop :=
  VelocitySafe R S ∧
  HumanDistanceSafe R S ∧
  CollisionRiskSafe R S


/- ============================================================
   5. Obverse-Reverse Consistency
   ============================================================ -/

/--
A coupled physical state is consistent when:

1. the physical state satisfies the formal law
2. the physical safety constraints hold
-/
def Consistent
    {X : Type*}
    {A : Type*}
    (Ψ : Psi X A) : Prop :=
  Ψ.math.Law Ψ.phys.state
    -- The state itself must satisfy the fundamental law.
    ∧
  PhysicallySafe Ψ.math Ψ.phys.state


/- ============================================================
   6. Harm Function
   ============================================================ -/

/--
General physical harm function.

Lower values represent lower physical risk.
-/
def Harm
    {X : Type*}
    (S : PhysicalState X) : ℝ :=
  S.collisionRisk
    + |S.velocity|
    + (1 / (S.humanDistance + 1))


/--
Extremal principle.

The selected state minimizes the specified harm function.
-/
def Extremal
    {X : Type*}
    (H : PhysicalState X → ℝ)
    (S₀ : PhysicalState X) : Prop :=
  ∀ S, H S₀ ≤ H S


/- ============================================================
   7. Action-Level Ethical Constraint
   ============================================================ -/

/--
Ethical permission for an action.

Unlike the original version, ethical evaluation is now
explicitly action-dependent.
-/
def EthicallyPermitted
    {X : Type*}
    {A : Type*}
    (Ψ : Psi X A)
    (a : A) : Prop :=
  Ψ.math.Law Ψ.phys.state a


/--
An action is executable only when both:

1. the physical state is safe
2. the proposed action satisfies the ethical law
-/
def SafetyAndEthicsSatisfied
    {X : Type*}
    {A : Type*}
    (Ψ : Psi X A)
    (a : A) : Prop :=
  PhysicallySafe Ψ.math Ψ.phys.state
    ∧
  EthicallyPermitted Ψ a


/- ============================================================
   8. Human Oversight
   ============================================================ -/

/--
Human oversight can approve or reject a specific action.
-/
structure HumanOversight
    (A : Type*) where

  approved : A → Prop


/--
Human approval of an action.
-/
def HumanApproved
    {A : Type*}
    (H : HumanOversight A)
    (a : A) : Prop :=
  H.approved a


/- ============================================================
   9. Confidence
   ============================================================ -/

/--
AI confidence represented as a value in [0,1].
-/
structure Confidence where

  value : ℝ

  lower :
    0 ≤ value

  upper :
    value ≤ 1


/--
Insufficient confidence triggers abstention.
-/
def ShouldAbstain
    (C : Confidence)
    (threshold : ℝ) : Prop :=
  C.value < threshold


/- ============================================================
   10. Decision
   ============================================================ -/

/--
The kernel has three logical outcomes:

EXECUTE
ABSTAIN
HALT
-/
inductive Decision
    (A : Type*)
  | execute : A → Decision A
  | abstain : Decision A
  | halt : Decision A


/- ============================================================
   11. Ethical Execution Gate
   ============================================================ -/

/--
Execution is permitted only if ALL conditions hold:

1. physical safety
2. ethical permission
3. human approval
4. sufficient confidence
-/
def ExecutionAllowed
    {X : Type*}
    {A : Type*}
    (Ψ : Psi X A)
    (O : HumanOversight A)
    (a : A)
    (C : Confidence)
    (threshold : ℝ) : Prop :=
  PhysicallySafe Ψ.math Ψ.phys.state
  ∧
  EthicallyPermitted Ψ a
  ∧
  HumanApproved O a
  ∧
  ¬ ShouldAbstain C threshold


/- ============================================================
   12. Ethical Controller
   ============================================================ -/

/--
Top-level ethical decision function.

If all requirements are satisfied:
    EXECUTE

If confidence is insufficient:
    ABSTAIN

Otherwise:
    HALT
-/
def EthicalController
    {X : Type*}
    {A : Type*}
    (Ψ : Psi X A)
    (O : HumanOversight A)
    (a : A)
    (C : Confidence)
    (threshold : ℝ) : Decision A :=
  if hSafe : PhysicallySafe Ψ.math Ψ.phys.state then
    if hEthical : EthicallyPermitted Ψ a then
      if hApproved : HumanApproved O a then
        if hConf : ¬ ShouldAbstain C threshold then
          Decision.execute a
        else
          Decision.abstain
      else
        Decision.halt
    else
      Decision.halt
  else
    Decision.halt


/- ============================================================
   13. Formal Safety Theorems
   ============================================================ -/

/--
An executable action necessarily satisfies physical safety.
-/
theorem execution_implies_physical_safety
    {X : Type*}
    {A : Type*}
    (Ψ : Psi X A)
    (O : HumanOversight A)
    (a : A)
    (C : Confidence)
    (threshold : ℝ)
    (h :
      ExecutionAllowed Ψ O a C threshold) :
    PhysicallySafe Ψ.math Ψ.phys.state := by

  exact h.1


/--
An executable action necessarily satisfies the ethical law.
-/
theorem execution_implies_ethical_permission
    {X : Type*}
    {A : Type*}
    (Ψ : Psi X A)
    (O : HumanOversight A)
    (a : A)
    (C : Confidence)
    (threshold : ℝ)
    (h :
      ExecutionAllowed Ψ O a C threshold) :
    EthicallyPermitted Ψ a := by

  exact h.2.1


/--
An executable action necessarily has human approval.
-/
theorem execution_implies_human_approval
    {X : Type*}
    {A : Type*}
    (Ψ : Psi X A)
    (O : HumanOversight A)
    (a : A)
    (C : Confidence)
    (threshold : ℝ)
    (h :
      ExecutionAllowed Ψ O a C threshold) :
    HumanApproved O a := by

  exact h.2.2.1


/--
An executable action necessarily has sufficient confidence.
-/
theorem execution_implies_confidence
    {X : Type*}
    {A : Type*}
    (Ψ : Psi X A)
    (O : HumanOversight A)
    (a : A)
    (C : Confidence)
    (threshold : ℝ)
    (h :
      ExecutionAllowed Ψ O a C threshold) :
    ¬ ShouldAbstain C threshold := by

  exact h.2.2.2


/- ============================================================
   14. Abstention Theorem
   ============================================================ -/

/--
Insufficient confidence prevents execution.
-/
theorem low_confidence_prevents_execution
    {X : Type*}
    {A : Type*}
    (Ψ : Psi X A)
    (O : HumanOversight A)
    (a : A)
    (C : Confidence)
    (threshold : ℝ)
    (hLow :
      ShouldAbstain C threshold) :
    ¬ ExecutionAllowed Ψ O a C threshold := by

  intro hExec
  exact hExec.2.2.2 hLow


/- ============================================================
   15. Ethical Invariant
   ============================================================ -/

/--
Central invariant:

An executable Physical AI action must satisfy
both physical safety and ethical permission.
-/
theorem ethical_execution_invariant
    {X : Type*}
    {A : Type*}
    (Ψ : Psi X A)
    (O : HumanOversight A)
    (a : A)
    (C : Confidence)
    (threshold : ℝ)
    (h :
      ExecutionAllowed Ψ O a C threshold) :
    PhysicallySafe Ψ.math Ψ.phys.state
      ∧
    EthicallyPermitted Ψ a := by

  exact ⟨h.1, h.2.1⟩


/- ============================================================
   16. F-Theory Physical AI Ethics Model
   ============================================================ -/

/--
Integrated model.

This retains the original F-Theory architecture while
adding the Physical AI ethical layer.
-/
structure PhysicalAIEthicsModel
    (X : Type*)
    (A : Type*) where

  Ψ : Psi X A

  /-- Minimum-harm physical state. -/
  S₀ : PhysicalState X

  extremal_condition :
    Extremal Harm S₀

  consistency_condition :
    Consistent Ψ

  oversight :
    HumanOversight A

  confidence :
    Confidence

  confidence_threshold :
    ℝ

  threshold_nonnegative :
    0 ≤ confidence_threshold

  threshold_upper :
    confidence_threshold ≤ 1


/- ============================================================
   17. Model Coherence
   ============================================================ -/

/--
The integrated model is internally coherent.
-/
theorem internal_coherence
    {X : Type*}
    {A : Type*}
    (M : PhysicalAIEthicsModel X A) :
    Extremal Harm M.S₀
      ∧
    Consistent M.Ψ := by

  exact ⟨
    M.extremal_condition,
    M.consistency_condition
  ⟩


/--
Consistency implies physical safety.
-/
theorem consistency_implies_safety
    {X : Type*}
    {A : Type*}
    (M : PhysicalAIEthicsModel X A) :
    PhysicallySafe M.Ψ.math M.Ψ.phys.state := by

  exact M.consistency_condition.2


/--
Consistency implies satisfaction of the formal law.
-/
theorem consistency_implies_law
    {X : Type*}
    {A : Type*}
    (M : PhysicalAIEthicsModel X A) :
    M.Ψ.math.Law M.Ψ.phys.state := by

  exact M.consistency_condition.1


/- ============================================================
   18. Final Physical AI Ethics Kernel
   ============================================================ -/

/--
Universal ethical decision interface.

The kernel does not implement the physical machine itself.

It determines whether a proposed physical action may
pass the ethical gate.

The actual actuator/controller can consume the resulting
Decision value.
-/
def PhysicalAIEthicsKernel
    {X : Type*}
    {A : Type*}
    (M : PhysicalAIEthicsModel X A)
    (a : A) : Decision A :=
  EthicalController
    M.Ψ
    M.oversight
    a
    M.confidence
    M.confidence_threshold


end FTheory
