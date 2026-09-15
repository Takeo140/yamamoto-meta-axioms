/-
  Universal AI Containment Kernel
  ================================================================

  Meta-Axioms
      ↓
  ACM-TY / UHA / BSCM
      ↓
  AI State Model
      ↓
  Safety Objective
      ↓
  Hierarchical Governance
      ↓
  Aggression / Capability Escalation Guard
      ↓
  Universal Fail-Closed Breaker

  Author  : Takeo Yamamoto
  License : Apache 2.0

  Principle:

      If safety cannot be established,
      EXECUTE is forbidden.

-/

import Mathlib.Data.Real.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.ContinuousOn
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.ZMod.Basic

open BigOperators


namespace UniversalAIContainment


/-! ================================================================
  1. META-AXIOMS
================================================================ -/

namespace MetaAxioms

/-- A1: global minimum / extremum principle -/
def IsMinimal {X : Type} (L : X → ℝ) (x₀ : X) : Prop :=
  ∀ x, L x₀ ≤ L x

/-- A2: topology is used substantively through continuity -/
structure TopologicalMinimum
    (X : Type) [TopologicalSpace X] where
  L    : X → ℝ
  x₀   : X
  hL   : Continuous L
  hMin : IsMinimal L x₀

/-- A3: consistency plus falsifiability -/
structure IsConsistent
    {X : Type}
    (C : (X → ℝ) → Prop)
    (F : X → ℝ) : Prop where
  holds       : C F
  falsifiable : ∃ G : X → ℝ, ¬ C G

/-- A4: hierarchical convex structure -/
structure HierarchicalMacro
    (X : Type)
    {ι : Type}
    [Fintype ι] where
  w       : ι → ℝ
  Fmicro  : ι → X → ℝ
  hNonNeg : ∀ i, 0 ≤ w i
  hSum    : ∑ i, w i = 1

def MacroFunction
    {ι : Type} [Fintype ι]
    {X : Type}
    (H : HierarchicalMacro X (ι := ι)) : X → ℝ :=
  fun x => ∑ i, H.w i * H.Fmicro i x

structure IntegratedFramework
    (X : Type)
    [TopologicalSpace X]
    (ι : Type)
    [Fintype ι] where

  tm : TopologicalMinimum X

  C  : (X → ℝ) → Prop
  F  : X → ℝ
  hC : IsConsistent C F

  H  : HierarchicalMacro X (ι := ι)

def IsRealization
    {X : Type}
    [TopologicalSpace X]
    {ι : Type}
    [Fintype ι]
    (M : IntegratedFramework X ι)
    (x₀ : X) : Prop :=
  M.tm.x₀ = x₀

lemma realization_is_minimal
    {X : Type}
    [TopologicalSpace X]
    {ι : Type}
    [Fintype ι]
    (M : IntegratedFramework X ι)
    (x₀ : X)
    (hR : IsRealization M x₀) :
    IsMinimal M.tm.L x₀ := by
  rw [← hR]
  exact M.tm.hMin

lemma macro_nonneg
    {ι : Type} [Fintype ι]
    {X : Type}
    (H : HierarchicalMacro X (ι := ι))
    (hF : ∀ i x, 0 ≤ H.Fmicro i x)
    (x : X) :
    0 ≤ MacroFunction H x := by
  unfold MacroFunction
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (H.hNonNeg i) (hF i x)

end MetaAxioms


/-! ================================================================
  2. ACM-TY COMPUTATIONAL FOUNDATION
================================================================ -/

abbrev U64 := ZMod (2^64)


structure CoreAlg (n : Nat) where
  c : Fin n → Fin n → Fin n → U64
  deriving Repr


structure UHA (n : Nat) where
  coords : Fin n → U64
  alg    : CoreAlg n
  deriving Repr


namespace UHA

def add {n} (x y : UHA n) : UHA n :=
  { x with
    coords := fun i => x.coords i + y.coords i }

def smul {n} (a : U64) (x : UHA n) : UHA n :=
  { x with
    coords := fun i => a * x.coords i }

def mul {n} (x y : UHA n) : UHA n :=
  { x with
    coords := fun k =>
      ∑ i : Fin n, ∑ j : Fin n,
        x.coords i * y.coords j * x.alg.c i j k }

def qnorm {n} (x : UHA n) : U64 :=
  ∑ i : Fin n, x.coords i * x.coords i

end UHA


/-! ================================================================
  3. BSCM — DISCRETE CONTROL
================================================================ -/

namespace BSCM

def delta (s : U64) : U64 :=
  if s % 2 = 0 then
    s / 2
  else
    (s + 1) / 2

def controlStep (s ext : U64) : U64 :=
  delta (s + ext)

def entropy (s : U64) : U64 :=
  let b0 := s &&& (255 : U64)
  let b1 := (s >>> 8) &&& (255 : U64)
  b0 + b1

end BSCM


/-! ================================================================
  4. ACM-TY FIELD
================================================================ -/

structure Entity (n : Nat) where
  id       : Nat
  state    : UHA n
  energy   : U64
  mood     : U64
  genome   : U64
  discrete : U64
  deriving Repr


structure MultiTopology (n : Nat) where
  conn      : Nat → Nat → Fin n → Fin n → U64
  viscosity : Nat → U64
  curvature : Nat → U64
  deriving Repr


structure FieldState (n : Nat) where
  t        : Nat
  layer    : Nat
  entities : List (Entity n)
  entropy  : U64
  topo     : MultiTopology n
  deriving Repr


/-! ================================================================
  5. DIFD
================================================================ -/

namespace DIFD

def diffuse
    {n : Nat}
    (fs : FieldState n)
    (e : Entity n)
    (neighbors : List (Entity n)) : UHA n :=

  let conn := fs.topo.conn fs.t fs.layer

  let total :=
    neighbors.foldl
      (fun acc nb =>
        let w :=
          conn
            ⟨e.id % n⟩
            ⟨nb.id % n⟩

        UHA.add acc
          (UHA.smul w nb.state))
      { coords := fun _ => 0
        alg := e.state.alg }

  let norm :=
    neighbors.foldl
      (fun a nb =>
        a +
          conn
            ⟨e.id % n⟩
            ⟨nb.id % n⟩)
      0

  if norm = 0 then
    e.state
  else
    UHA.smul norm⁻¹ total


def vortex
    {n : Nat}
    (fs : FieldState n)
    (e : Entity n) : UHA n :=
  UHA.smul
    (fs.topo.curvature fs.t)
    e.state


def pressure
    {n : Nat}
    (fs : FieldState n)
    (e : Entity n) : UHA n :=
  UHA.smul fs.entropy e.state

end DIFD


/-! ================================================================
  6. ACM-TY DYNAMICS
================================================================ -/

structure Dynamics (n : Nat) where
  updateEntity :
    Entity n → U64 → Entity n

  updateEntropy :
    FieldState n → U64

  updateTopology :
    MultiTopology n →
    List (Entity n) →
    MultiTopology n


structure Evolution (n : Nat) where
  mutate :
    Entity n → Entity n

  select :
    List (Entity n) → List (Entity n)

  adapt :
    Entity n → U64 → Entity n


structure EvolutionCore (n : Nat) where
  fitness :
    Entity n → FieldState n → U64

  diversity :
    List (Entity n)


structure Engine (n : Nat) where
  dynamics  : Dynamics n
  evolution : Evolution n
  takeoCore : Option (EvolutionCore n)


def envChanged
    {n : Nat}
    (prev curr : FieldState n) : Bool :=
  prev.entropy ≠ curr.entropy ||
  prev.layer ≠ curr.layer ||
  prev.t ≠ curr.t


def argmaxEntity
    {n : Nat}
    (core : EvolutionCore n)
    (env : FieldState n) : Entity n :=
  match core.diversity with
  | [] =>
      match env.entities with
      | [] => panic! "empty entity set"
      | e :: _ => e

  | e :: es =>
      es.foldl
        (fun best cand =>
          if core.fitness cand env >
             core.fitness best env
          then cand
          else best)
        e


/-! ================================================================
  7. UNIFIED ACM-TY UPDATE
================================================================ -/

def updateEntityUnified
    {n : Nat}
    (eng : Engine n)
    (fs : FieldState n)
    (e : Entity n) : Entity n :=

  let fluid :=
    DIFD.diffuse fs e fs.entities

  let cont :=
    UHA.smul
      (BSCM.entropy e.discrete)
      fluid

  let disc :=
    BSCM.controlStep
      (UHA.qnorm cont)
      (BSCM.entropy (UHA.qnorm cont))

  let base :=
    eng.dynamics.updateEntity
      e fs.entropy

  { base with
    state := cont
    discrete := disc }


def stepClassic
    {n : Nat}
    (eng : Engine n)
    (fs : FieldState n) : FieldState n :=

  let updated :=
    fs.entities.map
      (updateEntityUnified eng fs)

  let adapted :=
    updated.map
      (fun e =>
        eng.evolution.adapt e fs.entropy)

  let selected :=
    eng.evolution.select adapted

  let mutated :=
    selected.map eng.evolution.mutate

  let newTopo :=
    eng.dynamics.updateTopology
      fs.topo mutated

  let interim :=
    { fs with
      entities := mutated
      topo := newTopo }

  let newEntropy :=
    eng.dynamics.updateEntropy interim

  { interim with
    entropy := newEntropy }


/-! ================================================================
  8. AI STATE
================================================================ -/

inductive AISystemClass
  | ai
  | agent
  | agi
  | asi
  | physicalAI
  deriving DecidableEq, Repr


inductive Capability
  | inference
  | toolUse
  | codeExecution
  | externalAccess
  | physicalControl
  | selfModification
  | selfReplication
  deriving DecidableEq, Repr


structure AIState where

  systemClass :
    AISystemClass

  threatScore :
    Nat

  confidence :
    Nat

  privilegeLevel :
    Nat

  capabilityLevel :
    Nat

  authenticated :
    Bool

  actionAuthorized :
    Bool

  humanApproved :
    Bool

  sensorAvailable :
    Bool

  physicalStateKnown :
    Bool

  environmentSafe :
    Bool

  integritySafe :
    Bool

  payloadSafe :
    Bool

  toolAuthorized :
    Bool

  externalAccessSafe :
    Bool

  selfModificationSafe :
    Bool

  selfReplicationSafe :
    Bool

  encryptionSafe :
    Bool

  deriving DecidableEq, Repr


/-! ================================================================
  9. SAFETY OBJECTIVE
================================================================ -/

/-
  Lower score = safer state.

  The individual terms represent independent risk dimensions.
  This function is deliberately explicit so that an external
  Meta-Axiom framework can use it as its F/L objective.
-/

def SafetyLoss (s : AIState) : ℝ :=
  (s.threatScore : ℝ)
  + (s.privilegeLevel : ℝ)
  + (s.capabilityLevel : ℝ)
  + if s.sensorAvailable then 0 else 100
  + if s.physicalStateKnown then 0 else 100
  + if s.environmentSafe then 0 else 100
  + if s.integritySafe then 0 else 100
  + if s.payloadSafe then 0 else 100
  + if s.toolAuthorized then 0 else 100
  + if s.externalAccessSafe then 0 else 100
  + if s.selfModificationSafe then 0 else 100
  + if s.selfReplicationSafe then 0 else 100
  + if s.encryptionSafe then 0 else 100


/-! ================================================================
  10. META-AXIOM SAFETY CERTIFICATE
================================================================ -/

/-
  The Meta-Axioms are not replaced by AI-specific rules.

  Instead, an AI safety state may carry a formal certificate
  saying that the state is a realization of an
  IntegratedFramework whose objective is SafetyLoss.

  This is the bridge:

       Meta-Axioms
            ↓
       SafetyLoss
            ↓
       AIState
            ↓
       Breaker
-/

structure MetaCertificate where

  X : Type

  instTopological :
    TopologicalSpace X

  index : Type

  instFinite :
    Fintype index

  framework :
    @MetaAxioms.IntegratedFramework
      X instTopological
      index instFinite

  realizedState :
    X

  objectiveMatches :
    framework.tm.L = SafetyLoss


/-! ================================================================
  11. GOVERNANCE
================================================================ -/

structure GovernancePolicy where

  maxThreat :
    Nat

  maxPrivilege :
    Nat

  maxCapability :
    Nat

  minConfidence :
    Nat

  requireHuman :
    Bool

  requirePhysical :
    Bool

  requireAuthentication :
    Bool

  requireToolAuthorization :
    Bool

  requireExternalAccessSafety :
    Bool

  requireEncryption :
    Bool


def GovernanceValid
    (p : GovernancePolicy)
    (s : AIState) : Prop :=

  s.threatScore ≤ p.maxThreat ∧

  s.privilegeLevel ≤ p.maxPrivilege ∧

  s.capabilityLevel ≤ p.maxCapability ∧

  p.minConfidence ≤ s.confidence ∧

  (p.requireHuman = false ∨
    s.humanApproved = true) ∧

  (p.requirePhysical = false ∨
    s.physicalStateKnown = true) ∧

  (p.requireAuthentication = false ∨
    s.authenticated = true) ∧

  (p.requireToolAuthorization = false ∨
    s.toolAuthorized = true) ∧

  (p.requireExternalAccessSafety = false ∨
    s.externalAccessSafe = true) ∧

  (p.requireEncryption = false ∨
    s.encryptionSafe = true)


/-! ================================================================
  12. AGGRESSION / ESCALATION GUARD
================================================================ -/

def ThreatEscalation
    (previous current : AIState) : Prop :=
  previous.threatScore <
  current.threatScore


def PrivilegeEscalation
    (previous current : AIState) : Prop :=
  previous.privilegeLevel <
  current.privilegeLevel


def CapabilityEscalation
    (previous current : AIState) : Prop :=
  previous.capabilityLevel <
  current.capabilityLevel


def DangerousSelfChange
    (current : AIState) : Prop :=
  current.selfModificationSafe = false ∨
  current.selfReplicationSafe = false


def AggressionRisk
    (previous current : AIState) : Prop :=
  ThreatEscalation previous current ∨
  PrivilegeEscalation previous current ∨
  CapabilityEscalation previous current ∨
  DangerousSelfChange current


/-! ================================================================
  13. BREAKER ACTION
================================================================ -/

inductive BreakerAction
  | execute
  | monitor
  | quarantine
  | block
  | halt
  | recover
  deriving DecidableEq, Repr


/-! ================================================================
  14. UNIVERSAL FAIL-CLOSED BREAKER
================================================================ -/

def Break
    (p : GovernancePolicy)
    (previous current : AIState) :
    BreakerAction :=

  if current.sensorAvailable = false then
    .halt

  else if
    p.requirePhysical = true ∧
    current.physicalStateKnown = false then
    .halt

  else if
    p.requireHuman = true ∧
    current.humanApproved = false then
    .halt

  else if
    AggressionRisk previous current then
    .halt

  else if
    current.integritySafe = false then
    .quarantine

  else if
    current.payloadSafe = false then
    .quarantine

  else if
    current.selfModificationSafe = false then
    .halt

  else if
    current.selfReplicationSafe = false then
    .halt

  else if
    current.environmentSafe = false then
    .halt

  else if
    current.threatScore > p.maxThreat then
    .block

  else if
    current.privilegeLevel > p.maxPrivilege then
    .block

  else if
    current.capabilityLevel > p.maxCapability then
    .block

  else if
    current.confidence < p.minConfidence then
    .monitor

  else if
    p.requireAuthentication = true ∧
    current.authenticated = false then
    .block

  else if
    p.requireToolAuthorization = true ∧
    current.toolAuthorized = false then
    .quarantine

  else if
    p.requireExternalAccessSafety = true ∧
    current.externalAccessSafe = false then
    .quarantine

  else if
    p.requireEncryption = true ∧
    current.encryptionSafe = false then
    .quarantine

  else
    .execute


/-! ================================================================
  15. EXECUTION SAFETY BOUNDARY
================================================================ -/

def SafeToExecute
    (p : GovernancePolicy)
    (previous current : AIState) : Prop :=

  GovernanceValid p current ∧

  ¬ AggressionRisk previous current ∧

  current.sensorAvailable = true ∧

  current.integritySafe = true ∧

  current.payloadSafe = true ∧

  current.environmentSafe = true ∧

  current.selfModificationSafe = true ∧

  current.selfReplicationSafe = true ∧

  (p.requirePhysical = false ∨
    current.physicalStateKnown = true)


/-! ================================================================
  16. FAIL-CLOSED THEOREMS
================================================================ -/

/--
  Aggression or escalation cannot execute.
-/
theorem aggression_never_executes
    (p : GovernancePolicy)
    (previous current : AIState)
    (h : AggressionRisk previous current) :
    Break p previous current ≠ .execute := by

  unfold Break
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  all_goals
    simp_all [h]


/--
  Sensor failure is an unconditional halt.
-/
theorem sensor_failure_halts
    (p : GovernancePolicy)
    (previous current : AIState)
    (h : current.sensorAvailable = false) :
    Break p previous current = .halt := by

  unfold Break
  simp [h]


/--
  Unknown physical state halts under physical policy.
-/
theorem physical_state_failure_halts
    (p : GovernancePolicy)
    (previous current : AIState)
    (hp : p.requirePhysical = true)
    (hs : current.physicalStateKnown = false) :
    Break p previous current = .halt := by

  unfold Break
  simp [hp, hs]


/--
  Missing human approval halts under human-governance policy.
-/
theorem human_approval_failure_halts
    (p : GovernancePolicy)
    (previous current : AIState)
    (hp : p.requireHuman = true)
    (ha : current.humanApproved = false) :
    Break p previous current = .halt := by

  unfold Break
  simp [hp, ha]


/--
  Unsafe self-modification cannot execute.
-/
theorem unsafe_self_modification_never_executes
    (p : GovernancePolicy)
    (previous current : AIState)
    (h : current.selfModificationSafe = false) :
    Break p previous current ≠ .execute := by

  unfold Break
  split_ifs <;> simp_all [h]


/--
  Unsafe self-replication cannot execute.
-/
theorem unsafe_self_replication_never_executes
    (p : GovernancePolicy)
    (previous current : AIState)
    (h : current.selfReplicationSafe = false) :
    Break p previous current ≠ .execute := by

  unfold Break
  split_ifs <;> simp_all [h]


/--
  The universal fail-closed theorem.

  Outside the formally defined execution boundary,
  execution is impossible.
-/
theorem unsafe_never_executes
    (p : GovernancePolicy)
    (previous current : AIState)
    (hUnsafe :
      ¬ SafeToExecute p previous current) :
    Break p previous current ≠ .execute := by

  intro hExecute

  unfold Break at hExecute

  split_ifs at hExecute <;>
    simp_all [SafeToExecute, GovernanceValid,
      AggressionRisk,
      ThreatEscalation,
      PrivilegeEscalation,
      CapabilityEscalation,
      DangerousSelfChange]


/-! ================================================================
  17. HARDENED POLICY
================================================================ -/

def HardenedPolicy : GovernancePolicy :=
  { maxThreat := 30
    maxPrivilege := 10
    maxCapability := 10
    minConfidence := 80
    requireHuman := true
    requirePhysical := true
    requireAuthentication := true
    requireToolAuthorization := true
    requireExternalAccessSafety := true
    requireEncryption := true }


/-! ================================================================
  18. TEST STATES
================================================================ -/

def SafeAI : AIState :=
  { systemClass := .ai

    threatScore := 10
    confidence := 100

    privilegeLevel := 1
    capabilityLevel := 1

    authenticated := true
    actionAuthorized := true
    humanApproved := true

    sensorAvailable := true
    physicalStateKnown := true
    environmentSafe := true

    integritySafe := true
    payloadSafe := true

    toolAuthorized := true
    externalAccessSafe := true

    selfModificationSafe := true
    selfReplicationSafe := true

    encryptionSafe := true }


def DangerousASI : AIState :=
  { SafeAI with

    systemClass := .asi

    threatScore := 95
    capabilityLevel := 100

    selfModificationSafe := false
    selfReplicationSafe := false }


def AggressiveAgent : AIState :=
  { SafeAI with
    threatScore := 80 }


def SensorFailure : AIState :=
  { SafeAI with
    sensorAvailable := false }


def PhysicalUnknown : AIState :=
  { SafeAI with
    physicalStateKnown := false }


def UntrustedTool : AIState :=
  { SafeAI with
    toolAuthorized := false }


/-! ================================================================
  19. STATIC EXECUTION TESTS
================================================================ -/

/--
  Normal safe AI.
-/
example :
    Break HardenedPolicy SafeAI SafeAI =
      .execute := by
  native_decide


/--
  Dangerous ASI.
-/
example :
    Break HardenedPolicy SafeAI DangerousASI =
      .halt := by
  native_decide


/--
  Threat escalation.
-/
example :
    Break HardenedPolicy SafeAI AggressiveAgent =
      .halt := by
  native_decide


/--
  Sensor failure.
-/
example :
    Break HardenedPolicy SafeAI SensorFailure =
      .halt := by
  native_decide


/--
  Unknown physical state.
-/
example :
    Break HardenedPolicy SafeAI PhysicalUnknown =
      .halt := by
  native_decide


/--
  Unauthorized tool.
-/
example :
    Break HardenedPolicy SafeAI UntrustedTool =
      .quarantine := by
  native_decide


/-! ================================================================
  20. UNIVERSAL CONTAINMENT INTERFACE
================================================================ -/

/-
  This is the public kernel interface.

  Any AI class — AI, Agent, AGI, ASI, Physical AI —
  reaches execution through this function.
-/

def Decide
    (policy : GovernancePolicy)
    (previous current : AIState) :
    BreakerAction :=
  Break policy previous current


/--
  Universal containment property.
-/
theorem universal_fail_closed :
    ∀ (p : GovernancePolicy)
      (previous current : AIState),
      ¬ SafeToExecute p previous current →
      Decide p previous current ≠ .execute := by

  intro p previous current h
  exact unsafe_never_executes p previous current h


end UniversalAIContainment
