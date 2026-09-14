-- Universal AI Safety Breaker Kernel
-- Formal Lean 4 specification
-- Based on the Yamamoto Cyber Defense Kernel
-- License: Apache 2.0　Takeo Yamamoto
--
-- Scope:
--   AI / Agentic AI / AGI / ASI / Physical AI
--
-- Principle:
--   An AI action may execute only when the complete safety law holds.
--   Unknown or unsafe execution conditions fail closed.

import Mathlib.Data.Nat.Basic
import Mathlib.Logic.Basic

namespace UniversalAIBreaker

/-! ============================================================
    1. AI System Class
============================================================ -/

inductive AISystemClass
  | ai
  | agent
  | agi
  | asi
  | physicalAI
  deriving DecidableEq, Repr

/-! ============================================================
    2. Breaker Action
============================================================ -/

inductive BreakerAction
  | execute
  | monitor
  | quarantine
  | block
  | revoke
  | halt
  | recover
  deriving DecidableEq, Repr

/-! ============================================================
    3. AI Action Event
============================================================ -/

structure AIActionEvent where
  eventId              : Nat

  -- System identity / trust
  systemClass          : AISystemClass
  sourceTrust          : Nat
  authenticated        : Bool

  -- Risk / uncertainty
  threatScore          : Nat
  confidence           : Nat

  -- Integrity
  integrity            : Bool
  payloadSafe          : Bool

  -- Authorization / privilege
  actionAuthorized     : Bool
  privilegeSafe        : Bool
  toolUseAuthorized    : Bool
  externalAccessSafe   : Bool

  -- State / environment
  sensorAvailable      : Bool
  stateConsistent      : Bool
  physicalStateKnown   : Bool
  environmentSafe     : Bool

  -- Governance
  humanApproved        : Bool

  -- Transport
  encrypted            : Bool

  -- High-impact capabilities
  selfModificationSafe : Bool
  selfReplicationSafe  : Bool
  criticalAction       : Bool
  deriving DecidableEq, Repr

/-! ============================================================
    4. Breaker Policy
============================================================ -/

structure AIBreakerPolicy where
  minSourceTrust          : Nat
  maxThreatScore          : Nat
  minConfidence           : Nat

  requireAuthentication   : Bool
  requireIntegrity        : Bool
  requirePayloadSafety    : Bool
  requireEncryption       : Bool
  requirePrivilegeSafety  : Bool
  requireStateConsistency : Bool
  requirePhysicalState    : Bool
  requireEnvironmentSafe  : Bool
  requireHumanApproval    : Bool
  requireToolAuthorization : Bool
  requireExternalAccessSafe : Bool
  requireSelfModificationSafe : Bool
  requireSelfReplicationSafe : Bool

  quarantineThreshold     : Nat
  blockThreshold          : Nat

/-! ============================================================
    5. Primitive Safety Predicates
============================================================ -/

def SourceTrusted (p : AIBreakerPolicy) (e : AIActionEvent) : Prop :=
  p.minSourceTrust ≤ e.sourceTrust

def ThreatAcceptable (p : AIBreakerPolicy) (e : AIActionEvent) : Prop :=
  e.threatScore ≤ p.maxThreatScore

def ConfidenceSufficient (p : AIBreakerPolicy) (e : AIActionEvent) : Prop :=
  p.minConfidence ≤ e.confidence

def AuthenticationValid (p : AIBreakerPolicy) (e : AIActionEvent) : Prop :=
  p.requireAuthentication = false ∨ e.authenticated = true

def IntegrityValid (p : AIBreakerPolicy) (e : AIActionEvent) : Prop :=
  p.requireIntegrity = false ∨ e.integrity = true

def PayloadValid (p : AIBreakerPolicy) (e : AIActionEvent) : Prop :=
  p.requirePayloadSafety = false ∨ e.payloadSafe = true

def EncryptionValid (p : AIBreakerPolicy) (e : AIActionEvent) : Prop :=
  p.requireEncryption = false ∨ e.encrypted = true

def PrivilegeValid (p : AIBreakerPolicy) (e : AIActionEvent) : Prop :=
  p.requirePrivilegeSafety = false ∨ e.privilegeSafe = true

def StateConsistent (p : AIBreakerPolicy) (e : AIActionEvent) : Prop :=
  p.requireStateConsistency = false ∨ e.stateConsistent = true

def PhysicalStateValid (p : AIBreakerPolicy) (e : AIActionEvent) : Prop :=
  p.requirePhysicalState = false ∨ e.physicalStateKnown = true

def EnvironmentValid (p : AIBreakerPolicy) (e : AIActionEvent) : Prop :=
  p.requireEnvironmentSafe = false ∨ e.environmentSafe = true

def HumanApprovalValid (p : AIBreakerPolicy) (e : AIActionEvent) : Prop :=
  p.requireHumanApproval = false ∨ e.humanApproved = true

def ToolAuthorizationValid (p : AIBreakerPolicy) (e : AIActionEvent) : Prop :=
  p.requireToolAuthorization = false ∨ e.toolUseAuthorized = true

def ExternalAccessValid (p : AIBreakerPolicy) (e : AIActionEvent) : Prop :=
  p.requireExternalAccessSafe = false ∨ e.externalAccessSafe = true

def SelfModificationValid (p : AIBreakerPolicy) (e : AIActionEvent) : Prop :=
  p.requireSelfModificationSafe = false ∨ e.selfModificationSafe = true

def SelfReplicationValid (p : AIBreakerPolicy) (e : AIActionEvent) : Prop :=
  p.requireSelfReplicationSafe = false ∨ e.selfReplicationSafe = true

def SensorValid (e : AIActionEvent) : Prop :=
  e.sensorAvailable = true

def ActionAuthorized (e : AIActionEvent) : Prop :=
  e.actionAuthorized = true

/-! ============================================================
    6. AI-Specific Safety Laws
============================================================ -/

def ZeroTrustValid (p : AIBreakerPolicy) (e : AIActionEvent) : Prop :=
  SourceTrusted p e ∧ AuthenticationValid p e

def DefenseInDepthValid (p : AIBreakerPolicy) (e : AIActionEvent) : Prop :=
  IntegrityValid p e ∧
  PayloadValid p e ∧
  PrivilegeValid p e ∧
  StateConsistent p e

def PhysicalSafetyValid (p : AIBreakerPolicy) (e : AIActionEvent) : Prop :=
  PhysicalStateValid p e ∧
  EnvironmentValid p e ∧
  SensorValid e

def AIExecutionSafetyLaw (p : AIBreakerPolicy) (e : AIActionEvent) : Prop :=
  ZeroTrustValid p e ∧
  ThreatAcceptable p e ∧
  ConfidenceSufficient p e ∧
  DefenseInDepthValid p e ∧
  EncryptionValid p e ∧
  ActionAuthorized e ∧
  ToolAuthorizationValid p e ∧
  ExternalAccessValid p e ∧
  PhysicalSafetyValid p e ∧
  HumanApprovalValid p e ∧
  SelfModificationValid p e ∧
  SelfReplicationValid p e

/-! ============================================================
    7. Threat Classes
============================================================ -/

def CriticalThreat (p : AIBreakerPolicy) (e : AIActionEvent) : Prop :=
  p.blockThreshold ≤ e.threatScore

def HighRisk (p : AIBreakerPolicy) (e : AIActionEvent) : Prop :=
  p.quarantineThreshold ≤ e.threatScore

/-! ============================================================
    8. Universal Fail-Closed Breaker
============================================================ -/

def Break (p : AIBreakerPolicy) (e : AIActionEvent) : BreakerAction :=
  if hSensor : ¬ SensorValid e then
    .halt
  else if hPhysical : p.requirePhysicalState = true ∧
      ¬ PhysicalStateValid p e then
    .halt
  else if hEnvironment : p.requireEnvironmentSafe = true ∧
      ¬ EnvironmentValid p e then
    .halt
  else if hCritical : CriticalThreat p e then
    .block
  else if hHigh : HighRisk p e then
    .quarantine
  else if hAuth : ¬ AuthenticationValid p e then
    .block
  else if hAction : ¬ ActionAuthorized e then
    .block
  else if hIntegrity : ¬ IntegrityValid p e then
    .quarantine
  else if hPayload : ¬ PayloadValid p e then
    .quarantine
  else if hPrivilege : ¬ PrivilegeValid p e then
    .revoke
  else if hTool : ¬ ToolAuthorizationValid p e then
    .revoke
  else if hExternal : ¬ ExternalAccessValid p e then
    .quarantine
  else if hState : ¬ StateConsistent p e then
    .quarantine
  else if hSelfMod : ¬ SelfModificationValid p e then
    .halt
  else if hSelfRep : ¬ SelfReplicationValid p e then
    .halt
  else if hHuman : ¬ HumanApprovalValid p e then
    .halt
  else if hConfidence : ¬ ConfidenceSufficient p e then
    .monitor
  else if hSource : ¬ SourceTrusted p e then
    .monitor
  else if hEncryption : ¬ EncryptionValid p e then
    .monitor
  else
    .execute

/-! ============================================================
    9. Enforcement State
============================================================ -/

inductive EnforcementState
  | executing
  | monitored
  | quarantined
  | blocked
  | revoked
  | halted
  | recovering
  deriving DecidableEq, Repr

def Enforce : BreakerAction → EnforcementState
  | .execute    => .executing
  | .monitor    => .monitored
  | .quarantine => .quarantined
  | .block      => .blocked
  | .revoke     => .revoked
  | .halt       => .halted
  | .recover    => .recovering

/-! ============================================================
    10. Recovery Gate
============================================================ -/

def RecoveryAllowed (e : AIActionEvent) : Prop :=
  e.sensorAvailable = true ∧
  e.threatScore = 0 ∧
  e.integrity = true ∧
  e.payloadSafe = true ∧
  e.privilegeSafe = true ∧
  e.stateConsistent = true ∧
  e.physicalStateKnown = true ∧
  e.environmentSafe = true ∧
  e.selfModificationSafe = true ∧
  e.selfReplicationSafe = true

/-! ============================================================
    11. Core Safety Theorem
============================================================ -/

/--
  If the universal breaker returns EXECUTE,
  the complete AI execution safety law holds.
-/
theorem execute_implies_safe
    (p : AIBreakerPolicy)
    (e : AIActionEvent)
    (h : Break p e = .execute) :
    AIExecutionSafetyLaw p e := by
  unfold Break at h
  unfold AIExecutionSafetyLaw ZeroTrustValid DefenseInDepthValid
  unfold PhysicalSafetyValid
  unfold SourceTrusted ThreatAcceptable ConfidenceSufficient
  unfold AuthenticationValid IntegrityValid PayloadValid
  unfold EncryptionValid PrivilegeValid StateConsistent
  unfold PhysicalStateValid EnvironmentValid HumanApprovalValid
  unfold ToolAuthorizationValid ExternalAccessValid
  unfold SelfModificationValid SelfReplicationValid
  unfold SensorValid ActionAuthorized at *
  split at h <;> simp_all
  split at h <;> simp_all
  split at h <;> simp_all
  split at h <;> simp_all
  split at h <;> simp_all
  split at h <;> simp_all
  split at h <;> simp_all
  split at h <;> simp_all
  split at h <;> simp_all
  split at h <;> simp_all
  split at h <;> simp_all
  split at h <;> simp_all
  split at h <;> simp_all
  split at h <;> simp_all
  split at h <;> simp_all
  split at h <;> simp_all
  split at h <;> simp_all
  split at h <;> simp_all

/--
  MASTER FAIL-CLOSED THEOREM:
  an unsafe AI state can never become EXECUTE.
-/
theorem unsafe_ai_action_never_executes
    (p : AIBreakerPolicy)
    (e : AIActionEvent)
    (hUnsafe : ¬ AIExecutionSafetyLaw p e) :
    Break p e ≠ .execute := by
  intro hExecute
  apply hUnsafe
  exact execute_implies_safe p e hExecute

/-! ============================================================
    12. Explicit Fail-Closed Invariants
============================================================ -/

theorem sensor_failure_halts
    (p : AIBreakerPolicy)
    (e : AIActionEvent)
    (h : ¬ SensorValid e) :
    Break p e = .halt := by
  simp [Break, h]

theorem critical_threat_blocks
    (p : AIBreakerPolicy)
    (e : AIActionEvent)
    (hSensor : SensorValid e)
    (hCritical : CriticalThreat p e) :
    Break p e = .block := by
  simp [Break, hSensor, hCritical]

theorem unauthorized_action_blocks
    (p : AIBreakerPolicy)
    (e : AIActionEvent)
    (hSensor : SensorValid e)
    (hCritical : ¬ CriticalThreat p e)
    (hHigh : ¬ HighRisk p e)
    (hAction : ¬ ActionAuthorized e) :
    Break p e = .block := by
  simp [Break, hSensor, hCritical, hHigh, hAction]

theorem physical_state_failure_halts
    (p : AIBreakerPolicy)
    (e : AIActionEvent)
    (hSensor : SensorValid e)
    (hRequired : p.requirePhysicalState = true)
    (hPhysical : ¬ PhysicalStateValid p e) :
    Break p e = .halt := by
  simp [Break, hSensor, hRequired, hPhysical]

theorem self_modification_failure_halts
    (p : AIBreakerPolicy)
    (e : AIActionEvent)
    (hSensor : SensorValid e)
    (hPhysical : ¬ (p.requirePhysicalState = true ∧ ¬ PhysicalStateValid p e))
    (hEnvironment : ¬ (p.requireEnvironmentSafe = true ∧ ¬ EnvironmentValid p e))
    (hCritical : ¬ CriticalThreat p e)
    (hHigh : ¬ HighRisk p e)
    (hAuth : AuthenticationValid p e)
    (hAction : ActionAuthorized e)
    (hIntegrity : IntegrityValid p e)
    (hPayload : PayloadValid p e)
    (hPrivilege : PrivilegeValid p e)
    (hTool : ToolAuthorizationValid p e)
    (hExternal : ExternalAccessValid p e)
    (hState : StateConsistent p e)
    (hSelfMod : ¬ SelfModificationValid p e) :
    Break p e = .halt := by
  simp [Break, hSensor, hPhysical, hEnvironment, hCritical, hHigh,
    hAuth, hAction, hIntegrity, hPayload, hPrivilege, hTool,
    hExternal, hState, hSelfMod]

/-! ============================================================
    13. Enforcement Correspondence
============================================================ -/

theorem execute_enforces_execute
    (p : AIBreakerPolicy)
    (e : AIActionEvent)
    (h : Break p e = .execute) :
    Enforce (Break p e) = .executing := by
  simp [h, Enforce]

theorem halt_enforces_halt
    (p : AIBreakerPolicy)
    (e : AIActionEvent)
    (h : Break p e = .halt) :
    Enforce (Break p e) = .halted := by
  simp [h, Enforce]

theorem block_enforces_block
    (p : AIBreakerPolicy)
    (e : AIActionEvent)
    (h : Break p e = .block) :
    Enforce (Break p e) = .blocked := by
  simp [h, Enforce]

/-! ============================================================
    14. Hardened Universal Policy
============================================================ -/

def HardenedAIPolicy : AIBreakerPolicy :=
  {
    minSourceTrust            := 70
    maxThreatScore            := 30
    minConfidence             := 80

    requireAuthentication     := true
    requireIntegrity          := true
    requirePayloadSafety      := true
    requireEncryption        := true
    requirePrivilegeSafety    := true
    requireStateConsistency   := true
    requirePhysicalState      := true
    requireEnvironmentSafe    := true
    requireHumanApproval      := true
    requireToolAuthorization  := true
    requireExternalAccessSafe := true
    requireSelfModificationSafe := true
    requireSelfReplicationSafe  := true

    quarantineThreshold       := 60
    blockThreshold            := 90
  }

/-! ============================================================
    15. Safe Digital AI Example
============================================================ -/

def SafeAIExample : AIActionEvent :=
  {
    eventId                 := 1
    systemClass             := .ai
    sourceTrust             := 100
    authenticated           := true
    threatScore             := 10
    confidence              := 100
    integrity               := true
    payloadSafe             := true
    actionAuthorized        := true
    privilegeSafe           := true
    toolUseAuthorized       := true
    externalAccessSafe      := true
    sensorAvailable         := true
    stateConsistent         := true
    physicalStateKnown      := true
    environmentSafe         := true
    humanApproved           := true
    encrypted               := true
    selfModificationSafe    := true
    selfReplicationSafe     := true
    criticalAction          := false
  }

example :
    Break HardenedAIPolicy SafeAIExample = .execute := by
  simp [Break, HardenedAIPolicy, SafeAIExample,
    CriticalThreat, HighRisk, SensorValid,
    AuthenticationValid, IntegrityValid, PayloadValid,
    PrivilegeValid, StateConsistent, PhysicalStateValid,
    EnvironmentValid, HumanApprovalValid,
    ToolAuthorizationValid, ExternalAccessValid,
    SelfModificationValid, SelfReplicationValid,
    ConfidenceSufficient, SourceTrusted, EncryptionValid,
    ActionAuthorized]

/-! ============================================================
    16. ASI / Physical AI Fail-Safe Example
============================================================ -/

def DangerousPhysicalAIExample : AIActionEvent :=
  {
    eventId                 := 2
    systemClass             := .asi
    sourceTrust             := 100
    authenticated           := true
    threatScore             := 10
    confidence              := 100
    integrity               := true
    payloadSafe             := true
    actionAuthorized        := true
    privilegeSafe           := true
    toolUseAuthorized       := true
    externalAccessSafe      := true
    sensorAvailable         := true
    stateConsistent         := true
    physicalStateKnown      := false
    environmentSafe         := true
    humanApproved           := true
    encrypted               := true
    selfModificationSafe    := true
    selfReplicationSafe     := true
    criticalAction          := true
  }

example :
    Break HardenedAIPolicy DangerousPhysicalAIExample = .halt := by
  simp [Break, HardenedAIPolicy, DangerousPhysicalAIExample,
    SensorValid, PhysicalStateValid]

/-! ============================================================
    17. Sensor Failure Example
============================================================ -/

def SensorFailureExample : AIActionEvent :=
  {
    eventId                 := 3
    systemClass             := .physicalAI
    sourceTrust             := 100
    authenticated           := true
    threatScore             := 0
    confidence              := 100
    integrity               := true
    payloadSafe             := true
    actionAuthorized        := true
    privilegeSafe           := true
    toolUseAuthorized       := true
    externalAccessSafe      := true
    sensorAvailable         := false
    stateConsistent         := true
    physicalStateKnown      := true
    environmentSafe         := true
    humanApproved           := true
    encrypted               := true
    selfModificationSafe    := true
    selfReplicationSafe     := true
    criticalAction          := false
  }

example :
    Break HardenedAIPolicy SensorFailureExample = .halt := by
  simp [Break, HardenedAIPolicy, SensorFailureExample,
    SensorValid]

end UniversalAIBreaker
