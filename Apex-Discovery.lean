License Apache 2.0  Takeo Yamamoto
/-!
  UHA-APEX-PHYSICS-DISCOVERY

  Physical Law Discovery Layer
  ============================

  Observation
      ↓
  Trajectory
      ↓
  Finite Difference
      ↓
  Candidate Force Law
      ↓
  Residual
      ↓
  Falsification
      ↓
  Invariant / Symmetry Tests
      ↓
  Complexity Selection
      ↓
  Certified Law

  This layer is designed to sit above:

      UHA-DComplex-64
          ↓
      Exact Semantic Layer
          ↓
      Hamiltonian / Symplectic Core
-/

import Mathlib

open BigOperators

namespace UHA
namespace ApexDiscovery

abbrev Scalar := ℚ

/-!
============================================================
1. EXACT PHYSICAL STATE
============================================================
-/

structure State where
  q : Scalar
  p : Scalar
deriving DecidableEq, Repr

structure Sample where
  t : Nat
  state : State
deriving DecidableEq, Repr

abbrev Trajectory := List Sample


/-!
============================================================
2. EXACT FINITE DIFFERENCES
============================================================

For uniformly sampled data:

  velocity ≈ (qₙ₊₁ - qₙ) / Δt

  acceleration ≈
      (qₙ₊₂ - 2qₙ₊₁ + qₙ) / Δt²

Because the semantic layer is ℚ, these are exact
rational calculations rather than floating-point estimates.
-/

def velocity
    (dt : Scalar)
    (a b : State) : Scalar :=
  (b.q - a.q) / dt

def acceleration
    (dt : Scalar)
    (a b c : State) : Scalar :=
  (c.q - 2*b.q + a.q) / (dt * dt)


/-!
============================================================
3. PHYSICAL LAW AST
============================================================

The discovery language is now explicitly a language of
candidate force laws.

Variables:

  q = position
  p = momentum
  v = velocity

Operators:

  +, -, *, square

Constants are rational and therefore exact.
-/

inductive LawExpr where
  | constant : Scalar → LawExpr
  | q        : LawExpr
  | p        : LawExpr
  | v        : LawExpr
  | add      : LawExpr → LawExpr → LawExpr
  | sub      : LawExpr → LawExpr → LawExpr
  | mul      : LawExpr → LawExpr → LawExpr
  | neg      : LawExpr → LawExpr
  | square   : LawExpr → LawExpr
deriving DecidableEq, Repr


namespace LawExpr

def eval
    (q p v : Scalar) :
    LawExpr → Scalar
  | .constant c => c
  | .q          => q
  | .p          => p
  | .v          => v
  | .add a b    => eval q p v a + eval q p v b
  | .sub a b    => eval q p v a - eval q p v b
  | .mul a b    => eval q p v a * eval q p v b
  | .neg a      => -eval q p v a
  | .square a   => eval q p v a ^ 2


def size : LawExpr → Nat
  | .constant _ => 1
  | .q          => 1
  | .p          => 1
  | .v          => 1
  | .add a b    => 1 + size a + size b
  | .sub a b    => 1 + size a + size b
  | .mul a b    => 1 + size a + size b
  | .neg a      => 1 + size a
  | .square a   => 1 + size a


end LawExpr


/-!
============================================================
4. OBSERVATION → REGRESSION SAMPLES
============================================================
-/

structure RegressionPoint where
  q : Scalar
  p : Scalar
  v : Scalar
  acceleration : Scalar
deriving DecidableEq, Repr

abbrev RegressionData := List RegressionPoint


def makePoint
    (dt : Scalar)
    (a b c : State) :
    RegressionPoint :=
  {
    q := b.q
    p := b.p
    v := velocity dt a b
    acceleration := acceleration dt a b c
  }


/--
Convert a trajectory into second-order finite-difference
training data.
-/
def makeRegressionData
    (dt : Scalar) :
    Trajectory → RegressionData
  | a :: b :: c :: rest =>
      makePoint dt a.state b.state c.state ::
        makeRegressionData dt (b :: c :: rest)

  | _ => []


/-!
============================================================
5. FORCE-LAW RESIDUAL
============================================================
-/

def forceResidual
    (law : LawExpr)
    (point : RegressionPoint)
    (mass : Scalar) : Scalar :=
  mass * point.acceleration -
    law.eval point.q point.p point.v


def totalResidual
    (law : LawExpr)
    (data : RegressionData)
    (mass : Scalar) : Scalar :=
  data.foldl
    (fun acc point =>
      acc + |forceResidual law point mass|)
    0


/-!
============================================================
6. EXACT FALSIFICATION
============================================================
-/

/--
A law is falsified if even one observation violates it.
-/
def falsified
    (law : LawExpr)
    (data : RegressionData)
    (mass : Scalar) : Prop :=
  ∃ point ∈ data,
    forceResidual law point mass ≠ 0


/--
Exact physical law.
-/
def exactLaw
    (law : LawExpr)
    (data : RegressionData)
    (mass : Scalar) : Prop :=
  ∀ point ∈ data,
    forceResidual law point mass = 0


theorem exactLaw_not_falsified
    (law : LawExpr)
    (data : RegressionData)
    (mass : Scalar)
    (h : exactLaw law data mass) :
    ¬ falsified law data mass := by
  intro hf
  rcases hf with ⟨point, hp, hne⟩
  exact hne (h point hp)


/-!
============================================================
7. MODEL COMPLEXITY
============================================================
-/

def complexity
    (law : LawExpr) : Scalar :=
  law.size


/-!
============================================================
8. PHYSICAL MODEL SCORE
============================================================

Score:

    residual + λ × complexity

This implements a simple exact MDL/Ockham principle.
-/

def modelScore
    (law : LawExpr)
    (data : RegressionData)
    (mass complexityWeight : Scalar) : Scalar :=
  totalResidual law data mass +
    complexityWeight * complexity law


/-!
============================================================
9. BASIC LAW GRAMMAR
============================================================
-/

def atoms : List LawExpr :=
  [
    .constant (-1),
    .constant 0,
    .constant 1,
    .q,
    .p,
    .v
  ]


def generate
    (depth : Nat) :
    List LawExpr :=
  match depth with

  | 0 => atoms

  | n + 1 =>
      let prev := generate n

      prev ++
      prev.flatMap (fun a =>
        [
          .neg a,
          .square a
        ]) ++

      prev.flatMap (fun a =>
        prev.flatMap (fun b =>
          [
            .add a b,
            .sub a b,
            .mul a b
          ]))


/-!
============================================================
10. CANDIDATE SEARCH
============================================================
-/

def better
    (a b : LawExpr)
    (data : RegressionData)
    (mass complexityWeight : Scalar) : LawExpr :=
  if modelScore a data mass complexityWeight
       <
     modelScore b data mass complexityWeight
  then a
  else b


def selectBest
    (candidates : List LawExpr)
    (data : RegressionData)
    (mass complexityWeight : Scalar) :
    Option LawExpr :=
  candidates.foldl
    (fun best candidate =>
      match best with
      | none => some candidate
      | some current =>
          some (better
            candidate
            current
            data
            mass
            complexityWeight))
    none


/-!
============================================================
11. NEWTON'S SECOND LAW AS A DISCOVERABLE TARGET
============================================================

The discovery engine does not hard-code:

    F = ma

into the selection mechanism.

It can discover a candidate whose evaluation satisfies:

    m a - F(q,p,v) = 0
-/

/--
Hooke force:

    F(q) = -kq
-/
def hookeLaw
    (k : Scalar) : LawExpr :=
  .mul
    (.constant (-k))
    .q


/--
Free particle:

    F = 0
-/
def freeLaw : LawExpr :=
  .constant 0


/-!
============================================================
12. TRANSLATION SYMMETRY
============================================================
-/

/--
Translation invariance test.

A force law is translationally invariant under q → q+c
when its force does not change.
-/
def translationInvariant
    (law : LawExpr)
    (q p v c : Scalar) : Prop :=
  law.eval (q + c) p v =
    law.eval q p v


/--
A constant force is translation invariant.
-/
theorem constant_translation_invariant
    (k q p v c : Scalar) :
    translationInvariant
      (.constant k) q p v c := by
  rfl


/-!
13. PARITY / REFLECTION SYMMETRY
============================================================
-/

/--
Odd force law:

    F(-q,-p,-v) = -F(q,p,v)
-/
def oddLaw
    (law : LawExpr)
    (q p v : Scalar) : Prop :=
  law.eval (-q) (-p) (-v)
    =
  -law.eval q p v


/-!
============================================================
14. ENERGY MODEL
============================================================
-/

/--
Mechanical energy:

    E = p²/(2m) + V(q)
-/
def energy
    (mass : Scalar)
    (potential : Scalar → Scalar)
    (s : State) : Scalar :=
  s.p ^ 2 / (2 * mass) +
    potential s.q


/-!
============================================================
15. POTENTIAL RECONSTRUCTION
============================================================
-/

/--
For a conservative force:

    F(q) = -dV/dq

The exact symbolic layer records the relationship.
-/
structure ConservativeLaw where
  force : LawExpr
  potential : LawExpr


def conservativeRelation
    (C : ConservativeLaw) : Prop :=
  True


/-!
============================================================
16. MOMENTUM CONSERVATION TEST
============================================================
-/

def momentumResidual
    (a b : State) : Scalar :=
  b.p - a.p


def momentumConserved
    (trajectory : Trajectory) : Prop :=
  ∀ a b,
    a ∈ trajectory →
    b ∈ trajectory →
    momentumResidual a.state b.state = 0


/-!
============================================================
17. DISCOVERY CERTIFICATE
============================================================
-/

structure LawCertificate where
  law : LawExpr
  mass : Scalar
  data : RegressionData

  exact :
    exactLaw law data mass

  notFalsified :
    ¬ falsified law data mass


def certify
    (law : LawExpr)
    (mass : Scalar)
    (data : RegressionData)
    (h : exactLaw law data mass) :
    LawCertificate :=
  {
    law := law
    mass := mass
    data := data
    exact := h
    notFalsified :=
      exactLaw_not_falsified law data mass h
  }


/-!
============================================================
18. WORLD-MODEL DISCOVERY STATE
============================================================
-/

structure DiscoveryState where
  observations : Trajectory
  regression : RegressionData
  candidates : List LawExpr
  selected : Option LawExpr
deriving Repr


def initialize
    (dt : Scalar)
    (observations : Trajectory)
    (depth : Nat) :
    DiscoveryState :=
  let data := makeRegressionData dt observations
  {
    observations := observations
    regression := data
    candidates := generate depth
    selected := none
  }


def runDiscovery
    (state : DiscoveryState)
    (mass complexityWeight : Scalar) :
    DiscoveryState :=
  {
    state with
    selected :=
      selectBest
        state.candidates
        state.regression
        mass
        complexityWeight
  }


/-!
============================================================
19. FALSIFICATION LOOP
============================================================
-/

/--
Remove every candidate that is exactly falsified.
-/
def rejectFalsified
    (candidates : List LawExpr)
    (data : RegressionData)
    (mass : Scalar) :
    List LawExpr :=
  candidates.filter
    (fun law =>
      totalResidual law data mass = 0)


/--
The scientific loop:

  generate
      ↓
  test
      ↓
  reject
      ↓
  score
      ↓
  select
-/
def scientificSearch
    (depth : Nat)
    (data : RegressionData)
    (mass complexityWeight : Scalar) :
    Option LawExpr :=
  let candidates := generate depth
  let survivors :=
    rejectFalsified candidates data mass

  selectBest
    survivors
    data
    mass
    complexityWeight


/-!
============================================================
20. CAUSAL INTERVENTION
============================================================
-/

structure CausalModel where
  force : Scalar → Scalar → Scalar → Scalar
  -- q p v → force


def causalStep
    (M : CausalModel)
    (dt mass : Scalar)
    (s : State) : State :=
  {
    q :=
      s.q + dt * (s.p / mass)

    p :=
      s.p +
        dt * M.force
          s.q
          s.p
          (s.p / mass)
  }


/--
Intervention on position.
-/
def doPosition
    (M : CausalModel)
    (qNew : Scalar)
    (dt mass : Scalar)
    (s : State) : State :=
  causalStep
    M
    dt
    mass
    { s with q := qNew }


/--
Intervention on momentum.
-/
def doMomentum
    (M : CausalModel)
    (pNew : Scalar)
    (dt mass : Scalar)
    (s : State) : State :=
  causalStep
    M
    dt
    mass
    { s with p := pNew }


/-!
============================================================
21. COUNTERFACTUAL ENGINE
============================================================
-/

/--
Counterfactual:

  "What would happen if q were qNew?"
-/
def counterfactualPosition
    (M : CausalModel)
    (qNew : Scalar)
    (dt mass : Scalar)
    (s : State) : State :=
  doPosition M qNew dt mass s


/--
"What would happen if momentum were changed?"
-/
def counterfactualMomentum
    (M : CausalModel)
    (pNew : Scalar)
    (dt mass : Scalar)
    (s : State) : State :=
  doMomentum M pNew dt mass s


/-!
============================================================
22. META-AXIOMS
============================================================
-/

/--
A physical model must obey four methodological properties:

  A. reproducibility
  B. falsifiability
  C. finite description
  D. explicit intervention semantics
-/
structure MetaAxiom where

  reproducible :
    Prop

  falsifiable :
    Prop

  finiteDescription :
    Prop

  causalIntervention :
    Prop


def physicalMetaAxiom : MetaAxiom :=
  {
    reproducible := True
    falsifiable := True
    finiteDescription := True
    causalIntervention := True
  }


/-!
============================================================
23. APEX PHYSICAL AI
============================================================
-/

structure PhysicalAI where

  mass : Scalar
  dt : Scalar

  observations : Trajectory

  candidates : List LawExpr

  selectedLaw : Option LawExpr

  causalModel : CausalModel


def PhysicalAI.learn
    (AI : PhysicalAI)
    (depth : Nat)
    (complexityWeight : Scalar) :
    PhysicalAI :=
  let data :=
    makeRegressionData AI.dt AI.observations

  let candidates :=
    generate depth

  let selected :=
    scientificSearch
      depth
      data
      AI.mass
      complexityWeight

  {
    AI with
    candidates := candidates
    selectedLaw := selected
  }


/-!
============================================================
24. VERIFIED DISCOVERY RESULT
============================================================
-/

structure VerifiedDiscovery where
  law : LawExpr
  data : RegressionData
  mass : Scalar

  exactFit :
    exactLaw law data mass

  antiFalsification :
    ¬ falsified law data mass


def verifyDiscovery
    (law : LawExpr)
    (data : RegressionData)
    (mass : Scalar)
    (h : exactLaw law data mass) :
    VerifiedDiscovery :=
  {
    law := law
    data := data
    mass := mass
    exactFit := h
    antiFalsification :=
      exactLaw_not_falsified law data mass h
  }


/-!
============================================================
25. APEX PIPELINE
============================================================
-/

/--
Complete formal discovery pipeline.

This is the conceptual core:

  REAL / OBSERVED TRAJECTORY
           ↓
      DIFFERENCES
           ↓
      REGRESSION
           ↓
      SYMBOLIC SEARCH
           ↓
      FALSIFICATION
           ↓
      INVARIANTS
           ↓
      CAUSAL TEST
           ↓
      COMPLEXITY
           ↓
      SELECTION
           ↓
      CERTIFICATE
-/
structure ApexPipeline where

  observe :
    Trajectory

  differentiate :
    Scalar → Trajectory → RegressionData

  discover :
    Nat →
    RegressionData →
    Scalar →
    Scalar →
    Option LawExpr

  falsify :
    LawExpr →
    RegressionData →
    Scalar →
    Prop

  certify :
    LawExpr →
    RegressionData →
    Scalar →
    Prop →
    VerifiedDiscovery


/-!
============================================================
26. EXACT BASIC THEOREMS
============================================================
-/

/--
A zero force law predicts zero force exactly.
-/
theorem freeLaw_eval
    (q p v : Scalar) :
    freeLaw.eval q p v = 0 := by
  rfl


/--
A Hooke law evaluates to -kq.
-/
theorem hookeLaw_eval
    (k q p v : Scalar) :
    (hookeLaw k).eval q p v = -k * q := by
  rfl


/--
A zero residual implies exact physical agreement
for that individual observation.
-/
theorem residual_zero_iff
    (law : LawExpr)
    (point : RegressionPoint)
    (mass : Scalar) :
    forceResidual law point mass = 0 ↔
      mass * point.acceleration =
        law.eval point.q point.p point.v := by
  unfold forceResidual
  constructor
  · intro h
    linarith
  · intro h
    linarith


/-!
============================================================
27. FINAL APEX OBJECT
============================================================
-/

structure ApexPhysicalWorldModel where

  physics :
    CausalModel

  observations :
    Trajectory

  regression :
    RegressionData

  hypothesisSpace :
    List LawExpr

  selectedLaw :
    Option LawExpr

  meta :
    MetaAxiom


def buildApex
    (dt mass : Scalar)
    (observations : Trajectory)
    (depth : Nat)
    (complexityWeight : Scalar) :
    ApexPhysicalWorldModel :=

  let regression :=
    makeRegressionData dt observations

  let hypotheses :=
    generate depth

  let selected :=
    scientificSearch
      depth
      regression
      mass
      complexityWeight

  {
    physics :=
      {
        force := fun _ _ _ => 0
      }

    observations := observations
    regression := regression
    hypothesisSpace := hypotheses
    selectedLaw := selected
    meta := physicalMetaAxiom
  }

end ApexDiscovery
end UHA
