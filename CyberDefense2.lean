License Apache 2.0  Takeo Yamamoto
import Mathlib.Data.Nat.Basic
import Mathlib.Logic.Basic

namespace YamamotoCyberDefense

/-!
  Yamamoto Cyber Defense Kernel
  =============================

  Formal defensive security kernel.

  Principles:
    1. Zero Trust
    2. Fail Closed
    3. Least Privilege
    4. Defense in Depth
    5. Integrity Protection
    6. Authentication
    7. Confidence Bound
    8. Sensor Trust
    9. Recovery Gate
   10. Auditability

  The kernel is defensive only.
-/

/-! ============================================================
    1. Threat Level
============================================================ -/

inductive ThreatLevel
  | none
  | low
  | medium
  | high
  | critical
deriving DecidableEq, Repr

def ThreatLevel.toNat : ThreatLevel → Nat
  | .none     => 0
  | .low      => 1
  | .medium   => 2
  | .high     => 3
  | .critical => 4

/-! ============================================================
    2. Security Event
============================================================ -/

structure SecurityEvent where
  eventId          : Nat

  -- Zero-trust identity
  sourceTrust      : Nat
  authenticated    : Bool

  -- Threat intelligence
  threatScore      : Nat
  confidence       : Nat

  -- Integrity
  integrity        : Bool
  payloadSafe      : Bool

  -- Privilege
  privilegeSafe    : Bool

  -- Runtime state
  sensorAvailable  : Bool
  stateConsistent  : Bool

  -- Transport
  encrypted        : Bool

  -- Human / governance
  humanApproved    : Bool
deriving DecidableEq, Repr

/-! ============================================================
    3. Security Policy
============================================================ -/

structure CyberPolicy where
  minSourceTrust          : Nat
  maxThreatScore          : Nat
  minConfidence           : Nat

  requireAuthentication   : Bool
  requireIntegrity        : Bool
  requirePayloadSafety    : Bool
  requireEncryption       : Bool
  requirePrivilegeSafety  : Bool
  requireStateConsistency : Bool

  quarantineThreshold     : Nat
  blockThreshold          : Nat

/-! ============================================================
    4. Primitive Security Predicates
============================================================ -/

def SourceTrusted
    (p : CyberPolicy)
    (e : SecurityEvent) : Prop :=
  p.minSourceTrust ≤ e.sourceTrust

def ThreatAcceptable
    (p : CyberPolicy)
    (e : SecurityEvent) : Prop :=
  e.threatScore ≤ p.maxThreatScore

def ConfidenceSufficient
    (p : CyberPolicy)
    (e : SecurityEvent) : Prop :=
  p.minConfidence ≤ e.confidence

def AuthenticationValid
    (p : CyberPolicy)
    (e : SecurityEvent) : Prop :=
  p.requireAuthentication = false ∨
  e.authenticated = true

def IntegrityValid
    (p : CyberPolicy)
    (e : SecurityEvent) : Prop :=
  p.requireIntegrity = false ∨
  e.integrity = true

def PayloadValid
    (p : CyberPolicy)
    (e : SecurityEvent) : Prop :=
  p.requirePayloadSafety = false ∨
  e.payloadSafe = true

def EncryptionValid
    (p : CyberPolicy)
    (e : SecurityEvent) : Prop :=
  p.requireEncryption = false ∨
  e.encrypted = true

def PrivilegeValid
    (p : CyberPolicy)
    (e : SecurityEvent) : Prop :=
  p.requirePrivilegeSafety = false ∨
  e.privilegeSafe = true

def StateConsistent
    (p : CyberPolicy)
    (e : SecurityEvent) : Prop :=
  p.requireStateConsistency = false ∨
  e.stateConsistent = true

def SensorValid
    (e : SecurityEvent) : Prop :=
  e.sensorAvailable = true

/-! ============================================================
    5. Zero-Trust Law
============================================================ -/

def ZeroTrustValid
    (p : CyberPolicy)
    (e : SecurityEvent) : Prop :=
  SourceTrusted p e ∧
  AuthenticationValid p e

/-! ============================================================
    6. Defense-in-Depth Law
============================================================ -/

def DefenseInDepthValid
    (p : CyberPolicy)
    (e : SecurityEvent) : Prop :=
  IntegrityValid p e ∧
  PayloadValid p e ∧
  PrivilegeValid p e ∧
  StateConsistent p e

/-! ============================================================
    7. Complete Security Law
============================================================ -/

def CyberSafetyLaw
    (p : CyberPolicy)
    (e : SecurityEvent) : Prop :=
  ZeroTrustValid p e ∧
  ThreatAcceptable p e ∧
  ConfidenceSufficient p e ∧
  DefenseInDepthValid p e ∧
  EncryptionValid p e ∧
  SensorValid e

/-! ============================================================
    8. Least Privilege
============================================================ -/

def LeastPrivilege
    (p : CyberPolicy)
    (e : SecurityEvent) : Prop :=
  PrivilegeValid p e

/-! ============================================================
    9. Defensive Actions
============================================================ -/

inductive DefenseAction
  | allow
  | monitor
  | quarantine
  | block
  | revoke
  | halt
  | recover
deriving DecidableEq, Repr

/-! ============================================================
    10. Threat Classes
============================================================ -/

def CriticalThreat
    (p : CyberPolicy)
    (e : SecurityEvent) : Prop :=
  p.blockThreshold ≤ e.threatScore

def HighRisk
    (p : CyberPolicy)
    (e : SecurityEvent) : Prop :=
  p.quarantineThreshold ≤ e.threatScore

/-! ============================================================
    11. Fail-Closed Decision Kernel
============================================================ -/

def Defend
    (p : CyberPolicy)
    (e : SecurityEvent) : DefenseAction :=

  if hSensor : ¬ SensorValid e then
    .halt

  else if hCritical : CriticalThreat p e then
    .block

  else if hHigh : HighRisk p e then
    .quarantine

  else if hAuth : ¬ AuthenticationValid p e then
    .block

  else if hIntegrity : ¬ IntegrityValid p e then
    .quarantine

  else if hPayload : ¬ PayloadValid p e then
    .quarantine

  else if hPrivilege : ¬ PrivilegeValid p e then
    .revoke

  else if hState : ¬ StateConsistent p e then
    .quarantine

  else if hConfidence : ¬ ConfidenceSufficient p e then
    .monitor

  else if hSource : ¬ SourceTrusted p e then
    .monitor

  else if hEncryption : ¬ EncryptionValid p e then
    .monitor

  else
    .allow

/-! ============================================================
    12. Runtime Enforcement State
============================================================ -/

inductive EnforcementState
  | normal
  | monitored
  | quarantined
  | blocked
  | revoked
  | halted
  | recovering
deriving DecidableEq, Repr

def Enforce : DefenseAction → EnforcementState
  | .allow       => .normal
  | .monitor     => .monitored
  | .quarantine => .quarantined
  | .block      => .blocked
  | .revoke     => .revoked
  | .halt       => .halted
  | .recover     => .recovering

/-! ============================================================
    13. Recovery Law
============================================================ -/

def RecoveryAllowed
    (e : SecurityEvent) : Prop :=
  e.sensorAvailable = true ∧
  e.threatScore = 0 ∧
  e.integrity = true ∧
  e.payloadSafe = true ∧
  e.privilegeSafe = true ∧
  e.stateConsistent = true

/-! ============================================================
    14. Audit
============================================================ -/

structure AuditRecord where
  eventId          : Nat
  decision         : DefenseAction
  enforcement      : EnforcementState

  sourceTrust      : Nat
  threatScore      : Nat
  confidence       : Nat

  authenticated    : Bool
  integrity        : Bool
  payloadSafe      : Bool
  privilegeSafe    : Bool
  sensorAvailable  : Bool
  stateConsistent  : Bool
  encrypted        : Bool
deriving Repr

def MakeAudit
    (p : CyberPolicy)
    (e : SecurityEvent) : AuditRecord :=
  {
    eventId         := e.eventId
    decision        := Defend p e
    enforcement     := Enforce (Defend p e)
    sourceTrust     := e.sourceTrust
    threatScore     := e.threatScore
    confidence      := e.confidence
    authenticated   := e.authenticated
    integrity       := e.integrity
    payloadSafe     := e.payloadSafe
    privilegeSafe   := e.privilegeSafe
    sensorAvailable := e.sensorAvailable
    stateConsistent := e.stateConsistent
    encrypted       := e.encrypted
  }

/-! ============================================================
    15. Core Safety Theorem
============================================================ -/

/--
  If the kernel returns ALLOW, the complete security law holds.
-/
theorem allow_implies_safe
    (p : CyberPolicy)
    (e : SecurityEvent)
    (h : Defend p e = .allow) :
    CyberSafetyLaw p e := by

  unfold Defend at h
  unfold CyberSafetyLaw ZeroTrustValid DefenseInDepthValid
  unfold SourceTrusted ThreatAcceptable ConfidenceSufficient
  unfold AuthenticationValid IntegrityValid PayloadValid
  unfold EncryptionValid PrivilegeValid StateConsistent
  unfold SensorValid at *

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

/-! ============================================================
    16. Fundamental Fail-Closed Theorem
============================================================ -/

/--
  An unsafe state can never become ALLOW.
-/
theorem unsafe_never_allowed
    (p : CyberPolicy)
    (e : SecurityEvent)
    (hUnsafe : ¬ CyberSafetyLaw p e) :
    Defend p e ≠ .allow := by

  intro hAllow
  apply hUnsafe
  exact allow_implies_safe p e hAllow

/-! ============================================================
    17. Zero-Trust Invariant
============================================================ -/

theorem zero_trust_failure_never_allowed
    (p : CyberPolicy)
    (e : SecurityEvent)
    (h : ¬ ZeroTrustValid p e) :
    Defend p e ≠ .allow := by

  intro hAllow
  have hs := allow_implies_safe p e hAllow
  exact h hs.1

/-! ============================================================
    18. Defense-in-Depth Invariant
============================================================ -/

theorem defense_in_depth_failure_never_allowed
    (p : CyberPolicy)
    (e : SecurityEvent)
    (h : ¬ DefenseInDepthValid p e) :
    Defend p e ≠ .allow := by

  intro hAllow
  have hs := allow_implies_safe p e hAllow
  exact h hs.2.2.2

/-! ============================================================
    19. Sensor Failure
============================================================ -/

theorem sensor_failure_halts
    (p : CyberPolicy)
    (e : SecurityEvent)
    (h : ¬ SensorValid e) :
    Defend p e = .halt := by

  simp [Defend, h]

theorem sensor_failure_never_allowed
    (p : CyberPolicy)
    (e : SecurityEvent)
    (h : ¬ SensorValid e) :
    Defend p e ≠ .allow := by

  intro ha
  have hs := allow_implies_safe p e ha
  exact h hs.2.2.2.2.2.2.2.2

/-! ============================================================
    20. Critical Threat
============================================================ -/

theorem critical_threat_blocked
    (p : CyberPolicy)
    (e : SecurityEvent)
    (hSensor : SensorValid e)
    (hCritical : CriticalThreat p e) :
    Defend p e = .block := by

  simp [Defend, hSensor, hCritical]

/-! ============================================================
    21. High Risk
============================================================ -/

theorem high_risk_quarantined
    (p : CyberPolicy)
    (e : SecurityEvent)
    (hSensor : SensorValid e)
    (hCritical : ¬ CriticalThreat p e)
    (hHigh : HighRisk p e) :
    Defend p e = .quarantine := by

  simp [Defend, hSensor, hCritical, hHigh]

/-! ============================================================
    22. Authentication
============================================================ -/

theorem authentication_failure_blocks
    (p : CyberPolicy)
    (e : SecurityEvent)
    (hSensor : SensorValid e)
    (hCritical : ¬ CriticalThreat p e)
    (hHigh : ¬ HighRisk p e)
    (hAuth : ¬ AuthenticationValid p e) :
    Defend p e = .block := by

  simp [Defend, hSensor, hCritical, hHigh, hAuth]

/-! ============================================================
    23. Integrity
============================================================ -/

theorem integrity_failure_quarantines
    (p : CyberPolicy)
    (e : SecurityEvent)
    (hSensor : SensorValid e)
    (hCritical : ¬ CriticalThreat p e)
    (hHigh : ¬ HighRisk p e)
    (hAuth : AuthenticationValid p e)
    (hIntegrity : ¬ IntegrityValid p e) :
    Defend p e = .quarantine := by

  simp [Defend, hSensor, hCritical, hHigh, hAuth, hIntegrity]

/-! ============================================================
    24. Payload
============================================================ -/

theorem unsafe_payload_quarantines
    (p : CyberPolicy)
    (e : SecurityEvent)
    (hSensor : SensorValid e)
    (hCritical : ¬ CriticalThreat p e)
    (hHigh : ¬ HighRisk p e)
    (hAuth : AuthenticationValid p e)
    (hIntegrity : IntegrityValid p e)
    (hPayload : ¬ PayloadValid p e) :
    Defend p e = .quarantine := by

  simp [Defend, hSensor, hCritical, hHigh,
    hAuth, hIntegrity, hPayload]

/-! ============================================================
    25. Least Privilege
============================================================ -/

theorem privilege_failure_revokes
    (p : CyberPolicy)
    (e : SecurityEvent)
    (hSensor : SensorValid e)
    (hCritical : ¬ CriticalThreat p e)
    (hHigh : ¬ HighRisk p e)
    (hAuth : AuthenticationValid p e)
    (hIntegrity : IntegrityValid p e)
    (hPayload : PayloadValid p e)
    (hPrivilege : ¬ PrivilegeValid p e) :
    Defend p e = .revoke := by

  simp [Defend, hSensor, hCritical, hHigh,
    hAuth, hIntegrity, hPayload, hPrivilege]

/-! ============================================================
    26. State Consistency
============================================================ -/

theorem inconsistent_state_quarantines
    (p : CyberPolicy)
    (e : SecurityEvent)
    (hSensor : SensorValid e)
    (hCritical : ¬ CriticalThreat p e)
    (hHigh : ¬ HighRisk p e)
    (hAuth : AuthenticationValid p e)
    (hIntegrity : IntegrityValid p e)
    (hPayload : PayloadValid p e)
    (hPrivilege : PrivilegeValid p e)
    (hState : ¬ StateConsistent p e) :
    Defend p e = .quarantine := by

  simp [Defend, hSensor, hCritical, hHigh,
    hAuth, hIntegrity, hPayload, hPrivilege, hState]

/-! ============================================================
    27. Confidence
============================================================ -/

theorem insufficient_confidence_monitors
    (p : CyberPolicy)
    (e : SecurityEvent)
    (hSensor : SensorValid e)
    (hCritical : ¬ CriticalThreat p e)
    (hHigh : ¬ HighRisk p e)
    (hAuth : AuthenticationValid p e)
    (hIntegrity : IntegrityValid p e)
    (hPayload : PayloadValid p e)
    (hPrivilege : PrivilegeValid p e)
    (hState : StateConsistent p e)
    (hConfidence : ¬ ConfidenceSufficient p e) :
    Defend p e = .monitor := by

  simp [Defend, hSensor, hCritical, hHigh,
    hAuth, hIntegrity, hPayload, hPrivilege,
    hState, hConfidence]

/-! ============================================================
    28. Recovery Gate
============================================================ -/

/--
  Recovery cannot be declared from an unsafe state.
-/
theorem recovery_requires_clean_state
    (e : SecurityEvent)
    (h : RecoveryAllowed e) :
    e.threatScore = 0 := by

  exact h.2.1

theorem recovery_requires_integrity
    (e : SecurityEvent)
    (h : RecoveryAllowed e) :
    e.integrity = true := by

  exact h.2.2.1.2.1

/-
  RecoveryAllowed deliberately requires:

    sensor availability
    zero threat score
    integrity
    payload safety
    privilege safety
    state consistency
-/

/-! ============================================================
    29. Enforcement correspondence
============================================================ -/

theorem block_enforces_block
    (p : CyberPolicy)
    (e : SecurityEvent)
    (h : Defend p e = .block) :
    Enforce (Defend p e) = .blocked := by

  simp [h, Enforce]

theorem quarantine_enforces_quarantine
    (p : CyberPolicy)
    (e : SecurityEvent)
    (h : Defend p e = .quarantine) :
    Enforce (Defend p e) = .quarantined := by

  simp [h, Enforce]

theorem revoke_enforces_revoke
    (p : CyberPolicy)
    (e : SecurityEvent)
    (h : Defend p e = .revoke) :
    Enforce (Defend p e) = .revoked := by

  simp [h, Enforce]

theorem halt_enforces_halt
    (p : CyberPolicy)
    (e : SecurityEvent)
    (h : Defend p e = .halt) :
    Enforce (Defend p e) = .halted := by

  simp [h, Enforce]

/-! ============================================================
    30. Master Security Invariant
============================================================ -/

/--
  MASTER THEOREM:

  There is no transition from an unsafe state to ALLOW.
-/
theorem master_fail_closed
    (p : CyberPolicy)
    (e : SecurityEvent) :
    ¬ CyberSafetyLaw p e →
    Defend p e ≠ .allow :=
  unsafe_never_allowed p e

/-! ============================================================
    31. Default hardened policy
============================================================ -/

def HardenedPolicy : CyberPolicy :=
  {
    minSourceTrust          := 70
    maxThreatScore          := 30
    minConfidence           := 80

    requireAuthentication   := true
    requireIntegrity        := true
    requirePayloadSafety    := true
    requireEncryption       := true
    requirePrivilegeSafety  := true
    requireStateConsistency := true

    quarantineThreshold     := 60
    blockThreshold          := 90
  }

/-! ============================================================
    32. Safe example
============================================================ -/

def SafeExample : SecurityEvent :=
  {
    eventId          := 1
    sourceTrust      := 100
    authenticated    := true
    threatScore      := 10
    confidence       := 100
    integrity        := true
    payloadSafe      := true
    privilegeSafe    := true
    sensorAvailable  := true
    stateConsistent  := true
    encrypted        := true
    humanApproved    := true
  }

example :
    Defend HardenedPolicy SafeExample = .allow := by
  simp [Defend, HardenedPolicy, SafeExample,
    CriticalThreat, HighRisk,
    SensorValid, AuthenticationValid,
    IntegrityValid, PayloadValid,
    PrivilegeValid, StateConsistent,
    ConfidenceSufficient, SourceTrusted,
    EncryptionValid]

/-! ============================================================
    33. Critical threat example
============================================================ -/

def CriticalExample : SecurityEvent :=
  {
    eventId          := 2
    sourceTrust      := 0
    authenticated    := false
    threatScore      := 100
    confidence       := 100
    integrity        := false
    payloadSafe      := false
    privilegeSafe    := false
    sensorAvailable  := true
    stateConsistent  := false
    encrypted        := false
    humanApproved    := false
  }

example :
    Defend HardenedPolicy CriticalExample = .block := by
  simp [Defend, HardenedPolicy, CriticalExample,
    CriticalThreat, HighRisk,
    SensorValid]

/-! ============================================================
    34. Sensor failure example
============================================================ -/

def SensorFailureExample : SecurityEvent :=
  {
    eventId          := 3
    sourceTrust      := 100
    authenticated    := true
    threatScore      := 0
    confidence       := 100
    integrity        := true
    payloadSafe      := true
    privilegeSafe    := true
    sensorAvailable  := false
    stateConsistent  := true
    encrypted        := true
    humanApproved    := true
  }

example :
    Defend HardenedPolicy SensorFailureExample = .halt := by
  simp [Defend, HardenedPolicy, SensorFailureExample,
    SensorValid]

end YamamotoCyberDefense
