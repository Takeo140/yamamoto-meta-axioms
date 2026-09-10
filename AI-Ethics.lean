License Apache 2.0 Takeo Yamamoto
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.ContinuousOn
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Basic

open BigOperators

namespace AIEthics

/-!
# AI Ethics Kernel
A formal mathematical framework for constrained AI decision-making.

Derived from the Meta-Axioms framework:

A1: Minimize undesirable consequences.
A2: Ethical evaluation is continuous.
A3: Ethical constraints are consistent and falsifiable.
A4: Multiple ethical principles form a convex hierarchy.

Additional AI-specific principles:

E1: Harm minimization
E2: Hard safety constraints
E3: Human oversight
E4: Abstention under insufficient confidence
E5: Hierarchical ethical aggregation
-/

-- ============================================================
-- Basic types
-- ============================================================

/-- An AI state: environment, internal state, or decision context. -/
variable {X : Type}

/-- An AI action. -/
variable {A : Type}

/-- Ethical cost / undesirable consequence. -/
def Harm (X : Type) := X → ℝ

/-- Utility / beneficial consequence. -/
def Benefit (X : Type) := X → ℝ


-- ============================================================
-- E1: Harm Minimization
-- Derived from A1: Extremum Principle
-- ============================================================

/--
An action is ethically optimal when it globally minimizes
the specified harm function.
-/
def IsEthicallyMinimal
    (H : X → ℝ)
    (x₀ : X) : Prop :=
  ∀ x, H x₀ ≤ H x


/--
An ethical objective with a globally minimal state.
-/
structure EthicalObjective (X : Type) where
  harm : Harm X
  optimum : X
  hMinimal : IsEthicallyMinimal harm optimum


-- ============================================================
-- E2: Ethical Continuity
-- Derived from A2: Topology
-- ============================================================

/--
Ethical evaluation must be continuous.

This prevents arbitrarily discontinuous ethical responses
to infinitesimally different states.
-/
structure ContinuousEthicalObjective
    (X : Type)
    [TopologicalSpace X]
    extends EthicalObjective X where

  hContinuous : Continuous harm


-- ============================================================
-- E3: Ethical Consistency
-- Derived from A3
-- ============================================================

/--
An ethical constraint C is valid for F if:

1. F satisfies C.
2. There exists a possible state violating C.

The second condition prevents vacuous ethical rules.
-/
structure EthicalConsistency
    {X : Type}
    (C : (X → ℝ) → Prop)
    (F : X → ℝ) : Prop where

  satisfies :
    C F

  falsifiable :
    ∃ G : X → ℝ, ¬ C G


-- ============================================================
-- E4: Hierarchical Ethical Principles
-- Derived from A4
-- ============================================================

/--
A collection of ethical principles with convex weights.

Weights are non-negative and sum to one.
-/
structure EthicalHierarchy
    (X : Type)
    {ι : Type}
    [Fintype ι] where

  weight : ι → ℝ

  principle : ι → X → ℝ

  weight_nonneg :
    ∀ i, 0 ≤ weight i

  weight_sum :
    ∑ i, weight i = 1


/--
Aggregate ethical cost.

This is the mathematical "ethical score" used by the AI.
-/
def EthicalScore
    {ι : Type}
    [Fintype ι]
    {X : Type}
    (E : EthicalHierarchy X (ι := ι)) :
    X → ℝ :=
  fun x =>
    ∑ i, E.weight i * E.principle i x


-- ============================================================
-- E5: Hard Safety Constraints
-- ============================================================

/--
A hard ethical constraint may never be violated.

Unlike weighted principles, this is not traded away
against other objectives.
-/
structure SafetyConstraint (X : Type) where

  safe : X → Prop

  nonempty :
    ∃ x, safe x


/--
An action/state satisfies a safety constraint.
-/
def IsSafe
    {X : Type}
    (S : SafetyConstraint X)
    (x : X) : Prop :=
  S.safe x


-- ============================================================
-- E6: Human Oversight
-- ============================================================

/--
Human oversight is represented as an explicit approval predicate.

An AI action cannot be considered fully authorized unless
the relevant human authority approves it.
-/
structure HumanOversight
    (X : Type) where

  approved : X → Prop


/--
An AI state is authorized only when human approval exists.
-/
def IsHumanApproved
    {X : Type}
    (O : HumanOversight X)
    (x : X) : Prop :=
  O.approved x


-- ============================================================
-- E7: Abstention
-- ============================================================

/--
The AI may abstain when confidence is insufficient.

This is important because an ethical AI must have an action
other than "execute."
-/
inductive Decision (A : Type)
  | execute : A → Decision A
  | abstain : Decision A


/--
Confidence value in [0,1].
-/
structure Confidence where

  value : ℝ

  lower :
    0 ≤ value

  upper :
    value ≤ 1


/--
An AI decision policy.
-/
structure AIPolicy
    (X : Type)
    (A : Type) where

  action : X → A

  confidence : X → Confidence


-- ============================================================
-- E8: Ethical Decision
-- ============================================================

/--
A fully constrained AI decision.

Execution requires:

1. safety
2. ethical admissibility
3. human approval
4. sufficient confidence

Otherwise the system may abstain.
-/
structure EthicalDecision
    (X : Type)
    (A : Type) where

  state : X

  action : A

  safe : Prop

  ethical : Prop

  approved : Prop

  confidence : Confidence


-- ============================================================
-- Unified AI Ethics Framework
-- ============================================================

structure AIEthicsFramework
    (X : Type)
    [TopologicalSpace X]
    {ι : Type}
    [Fintype ι] where

  -- A1 / E1
  objective :
    ContinuousEthicalObjective X

  -- A3 / E3
  constraint :
    (X → ℝ) → Prop

  reference :
    X → ℝ

  consistency :
    EthicalConsistency constraint reference

  -- A4 / E4
  hierarchy :
    EthicalHierarchy X (ι := ι)

  -- E2
  safety :
    SafetyConstraint X

  -- E6
  oversight :
    HumanOversight X


-- ============================================================
-- Ethical Admissibility
-- ============================================================

/--
A state is ethically admissible only if it satisfies
the hard safety condition and human oversight.

The weighted ethical score is evaluated separately.
-/
def EthicallyAdmissible
    {X : Type}
    [TopologicalSpace X]
    {ι : Type}
    [Fintype ι]
    (M : AIEthicsFramework X (ι := ι))
    (x : X) : Prop :=
  M.safety.safe x ∧
  M.oversight.approved x


-- ============================================================
-- Ethical Realization
-- ============================================================

/--
The framework is realized when the selected state is
the minimum-harm state and satisfies all hard constraints.
-/
def IsEthicalRealization
    {X : Type}
    [TopologicalSpace X]
    {ι : Type}
    [Fintype ι]
    (M : AIEthicsFramework X (ι := ι))
    (x : X) : Prop :=
  M.objective.optimum = x ∧
  EthicallyAdmissible M x


-- ============================================================
-- Core Theorems
-- ============================================================

/--
The ethical optimum minimizes the specified harm function.
-/
lemma ethical_optimum_minimizes_harm
    {X : Type}
    [TopologicalSpace X]
    {ι : Type}
    [Fintype ι]
    (M : AIEthicsFramework X (ι := ι)) :
    IsEthicallyMinimal
      M.objective.harm
      M.objective.optimum :=
  M.objective.hMinimal


/--
An ethical realization is safe.
-/
lemma ethical_realization_is_safe
    {X : Type}
    [TopologicalSpace X]
    {ι : Type}
    [Fintype ι]
    (M : AIEthicsFramework X (ι := ι))
    (x : X)
    (h : IsEthicalRealization M x) :
    M.safety.safe x := by

  rcases h with ⟨hx, hs, ho⟩
  exact hs


/--
An ethical realization has human approval.
-/
lemma ethical_realization_is_approved
    {X : Type}
    [TopologicalSpace X]
    {ι : Type}
    [Fintype ι]
    (M : AIEthicsFramework X (ι := ι))
    (x : X)
    (h : IsEthicalRealization M x) :
    M.oversight.approved x := by

  rcases h with ⟨hx, hs, ho⟩
  exact ho


-- ============================================================
-- Convexity of Ethical Aggregation
-- ============================================================

/--
If every ethical principle assigns non-negative cost,
then the aggregate ethical score is non-negative.
-/
lemma ethical_score_nonneg
    {X : Type}
    {ι : Type}
    [Fintype ι]
    (E : EthicalHierarchy X (ι := ι))
    (hP :
      ∀ i x, 0 ≤ E.principle i x)
    (x : X) :
    0 ≤ EthicalScore E x := by

  unfold EthicalScore

  apply Finset.sum_nonneg

  intro i hi

  exact mul_nonneg
    (E.weight_nonneg i)
    (hP i x)


-- ============================================================
-- Ethical Safety Theorem
-- ============================================================

/--
A realized ethical decision cannot violate the hard
safety constraint.
-/
theorem safety_invariant
    {X : Type}
    [TopologicalSpace X]
    {ι : Type}
    [Fintype ι]
    (M : AIEthicsFramework X (ι := ι))
    (x : X)
    (hR : IsEthicalRealization M x) :
    IsSafe M.safety x := by

  exact ethical_realization_is_safe M x hR


-- ============================================================
-- Human Oversight Invariant
-- ============================================================

/--
A realized ethical decision requires human approval.
-/
theorem human_oversight_invariant
    {X : Type}
    [TopologicalSpace X]
    {ι : Type}
    [Fintype ι]
    (M : AIEthicsFramework X (ι := ι))
    (x : X)
    (hR : IsEthicalRealization M x) :
    IsHumanApproved M.oversight x := by

  exact ethical_realization_is_approved M x hR


-- ============================================================
-- Abstention Principle
-- ============================================================

/--
If confidence is zero, execution is not required.
The system may abstain.

This theorem deliberately does not force execution.
-/
def ShouldAbstain
    (c : Confidence)
    (threshold : ℝ) : Prop :=
  c.value < threshold


-- ============================================================
-- Final AI Ethical Kernel
-- ============================================================

/--
The central ethical kernel:

An AI should execute only when the state is:

1. harm-minimizing,
2. safe,
3. human-approved.

Otherwise abstention remains available.
-/
def CanExecuteEthically
    {X : Type}
    [TopologicalSpace X]
    {ι : Type}
    [Fintype ι]
    (M : AIEthicsFramework X (ι := ι))
    (x : X) : Prop :=
  IsEthicalRealization M x


end AIEthics
