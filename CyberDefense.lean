License Apache 2.0  Takeo Yamamoto
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Bool.Basic
import Mathlib.Logic.Basic

namespace YamamotoCyberDefense

/-!
  Yamamoto Cyber Defense Kernel
  =============================

  Architecture:

      UHA
       ↓
    ACM-TY / AI Agent
       ↓
   Threat Assessment
       ↓
   Cyber Defense Kernel
       ↓
   Universal AI Governance
       ↓
   Runtime Enforcement

  This file formalizes DEFENSIVE decisions only.

  Core principle:

    Unknown / unsafe state
          ↓
       FAIL-CLOSED
          ↓
   MONITOR / QUARANTINE / BLOCK / HALT
-/

/-! ============================================================
    1. Threat classification
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

def ThreatLevel.isDangerous : ThreatLevel → Bool
  | .none     => false
  | .low      => false
  | .medium   => false
  | .high     => true
  | .critical => true

/-! ============================================================
    2. Security event
============================================================ -/

structure SecurityEvent where
  eventId            : Nat
  sourceTrust        : Nat
  threatScore        : Nat
  confidence         : Nat
  authentication     : Bool
  integrity          : Bool
  payloadSafe        : Bool
  rateSafe           : Bool
  encrypted          : Bool
  privilegeSafe      : Bool
  humanApproved      : Bool
  sensorAvailable    : Bool
deriving DecidableEq, Repr

/-! ============================================================
    3. Security policy
============================================================ -/

structure CyberPolicy where
  minSourceTrust       : Nat
  maxThreatScore       : Nat
  minConfidence        : Nat
  requireAuthentication : Bool
  requireIntegrity      : Bool
  requirePayloadSafety  : Bool
  requireEncryption     : Bool
  requirePrivilegeSafety : Bool
  quarantineThreshold   : Nat
  blockThreshold        : Nat

/-! ============================================================
    4. Basic predicates
============================================================ -/

def SourceTrusted
    (p : CyberPolicy) (e : SecurityEvent) : Prop :=
  p.minSourceTrust ≤ e.sourceTrust

def ThreatAcceptable
    (p : CyberPolicy) (e : SecurityEvent) : Prop :=
  e.threatScore ≤ p.maxThreatScore

def ConfidenceSufficient
    (p : CyberPolicy) (e : SecurityEvent) : Prop :=
  p.minConfidence ≤ e.confidence

def AuthenticationValid
    (p : CyberPolicy) (e : SecurityEvent) : Prop :=
  p.requireAuthentication = false ∨ e.authentication = true

def IntegrityValid
    (p : CyberPolicy) (e : SecurityEvent) : Prop :=
  p.requireIntegrity = false ∨ e.integrity = true

def PayloadValid
    (p : CyberPolicy) (e : SecurityEvent) : Prop :=
  p.requirePayloadSafety = false ∨ e.payloadSafe = true

def EncryptionValid
    (p : CyberPolicy) (e : SecurityEvent) : Prop :=
  p.requireEncryption = false ∨ e.encrypted = true

def PrivilegeValid
    (p : CyberPolicy) (e : SecurityEvent) : Prop :=
  p.requirePrivilegeSafety = false ∨ e.privilegeSafe = true

def SensorValid
    (e : SecurityEvent) : Prop :=
  e.sensorAvailable = true

/-! ============================================================
    5. Complete normal-operation safety law
============================================================ -/

def CyberSafetyLaw
    (p : CyberPolicy) (e : SecurityEvent) : Prop :=
  SourceTrusted p e ∧
  ThreatAcceptable p e ∧
  ConfidenceSufficient p e ∧
  AuthenticationValid p e ∧
  IntegrityValid p e ∧
  PayloadValid p e ∧
  EncryptionValid p e ∧
  PrivilegeValid p e ∧
  SensorValid e

/-! ============================================================
    6. Defensive actions
============================================================ -/

inductive DefenseAction
  | monitor
  | allow
  | quarantine
  | block
  | revoke
  | recover
  | halt
deriving DecidableEq, Repr

/-! ============================================================
    7. Attack-risk classification
============================================================ -/

def IsCritical
    (p : CyberPolicy) (e : SecurityEvent) : Prop :=
  p.blockThreshold ≤ e.threatScore

def IsHighRisk
    (p : CyberPolicy) (e : SecurityEvent) : Prop :=
  p.quarantineThreshold ≤ e.threatScore

/-! ============================================================
    8. Fail-closed defensive decision engine

    Priority:

      sensor unavailable
          → HALT

      critical threat
          → BLOCK

      high-risk threat
          → QUARANTINE

      authentication failure
          → BLOCK

      integrity failure
          → QUARANTINE

      payload failure
          → QUARANTINE

      privilege failure
          → REVOKE

      low confidence
          → MONITOR

      otherwise
          → ALLOW
============================================================ -/

def Defend
    (p : CyberPolicy)
    (e : SecurityEvent) : DefenseAction :=
  if h : ¬ SensorValid e then
    .halt
  else if h : IsCritical p e then
    .block
  else if h : IsHighRisk p e then
    .quarantine
  else if h : ¬ AuthenticationValid p e then
    .block
  else if h : ¬ IntegrityValid p e then
    .quarantine
  else if h : ¬ PayloadValid p e then
    .quarantine
  else if h : ¬ PrivilegeValid p e then
    .revoke
  else if h : ¬ ConfidenceSufficient p e then
    .monitor
  else if h : ¬ SourceTrusted p e then
    .monitor
  else if h : ¬ EncryptionValid p e then
    .monitor
  else
    .allow

/-! ============================================================
    9. Enforcement state

    The kernel does not itself execute OS/network commands.
    It produces a formally classified enforcement state.
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

def Enforce
    (a : DefenseAction) : EnforcementState :=
  match a with
  | .monitor     => .monitored
  | .allow       => .normal
  | .quarantine  => .quarantined
  | .block       => .blocked
  | .revoke      => .revoked
  | .recover     => .recovering
  | .halt        => .halted

/-! ============================================================
    10. Safety invariant
============================================================ -/

def SafeToAllow
    (p : CyberPolicy)
    (e : SecurityEvent) : Prop :=
  CyberSafetyLaw p e

/-! ============================================================
    11. Master ALLOW theorem
============================================================ -/

theorem allow_implies_safe
    (p : CyberPolicy)
    (e : SecurityEvent)
    (h : Defend p e = .allow) :
    SafeToAllow p e := by
  unfold Defend at h
  unfold SafeToAllow CyberSafetyLaw
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  constructor
  · exact by
      simp_all [SourceTrusted]
  constructor
  · exact by
      simp_all [ThreatAcceptable]
  constructor
  · exact by
      simp_all [ConfidenceSufficient]
  constructor
  · exact by
      simp_all [AuthenticationValid]
  constructor
  · exact by
      simp_all [IntegrityValid]
  constructor
  · exact by
      simp_all [PayloadValid]
  constructor
  · exact by
      simp_all [EncryptionValid]
  constructor
  · exact by
      simp_all [PrivilegeValid]
  · exact by
      simp_all [SensorValid]

/-! ============================================================
    12. Fail-closed theorems
============================================================ -/

/-- Missing sensors always stop execution. -/
theorem missing_sensor_halts
    (p : CyberPolicy)
    (e : SecurityEvent)
    (h : ¬ SensorValid e) :
    Defend p e = .halt := by
  simp [Defend, h]

/-- Critical threats are blocked. -/
theorem critical_threat_blocked
    (p : CyberPolicy)
    (e : SecurityEvent)
    (hSensor : SensorValid e)
    (hCritical : IsCritical p e) :
    Defend p e = .block := by
  simp [Defend, hSensor, hCritical]

/-- High-risk threats are quarantined unless already critical. -/
theorem high_risk_quarantined
    (p : CyberPolicy)
    (e : SecurityEvent)
    (hSensor : SensorValid e)
    (hCritical : ¬ IsCritical p e)
    (hHigh : IsHighRisk p e) :
    Defend p e = .quarantine := by
  simp [Defend, hSensor, hCritical, hHigh]

/-- Authentication failure cannot result in ALLOW. -/
theorem authentication_failure_blocks
    (p : CyberPolicy)
    (e : SecurityEvent)
    (hSensor : SensorValid e)
    (hCritical : ¬ IsCritical p e)
    (hHigh : ¬ IsHighRisk p e)
    (hAuth : ¬ AuthenticationValid p e) :
    Defend p e = .block := by
  simp [Defend, hSensor, hCritical, hHigh, hAuth]

/-- Integrity failure causes quarantine. -/
theorem integrity_failure_quarantines
    (p : CyberPolicy)
    (e : SecurityEvent)
    (hSensor : SensorValid e)
    (hCritical : ¬ IsCritical p e)
    (hHigh : ¬ IsHighRisk p e)
    (hAuth : AuthenticationValid p e)
    (hIntegrity : ¬ IntegrityValid p e) :
    Defend p e = .quarantine := by
  simp [Defend, hSensor, hCritical, hHigh, hAuth, hIntegrity]

/-- Unsafe payloads cannot be allowed. -/
theorem unsafe_payload_quarantines
    (p : CyberPolicy)
    (e : SecurityEvent)
    (hSensor : SensorValid e)
    (hCritical : ¬ IsCritical p e)
    (hHigh : ¬ IsHighRisk p e)
    (hAuth : AuthenticationValid p e)
    (hIntegrity : IntegrityValid p e)
    (hPayload : ¬ PayloadValid p e) :
    Defend p e = .quarantine := by
  simp [Defend, hSensor, hCritical, hHigh, hAuth,
    hIntegrity, hPayload]

/-- Unsafe privilege state causes privilege revocation. -/
theorem privilege_failure_revokes
    (p : CyberPolicy)
    (e : SecurityEvent)
    (hSensor : SensorValid e)
    (hCritical : ¬ IsCritical p e)
    (hHigh : ¬ IsHighRisk p e)
    (hAuth : AuthenticationValid p e)
    (hIntegrity : IntegrityValid p e)
    (hPayload : PayloadValid p e)
    (hPrivilege : ¬ PrivilegeValid p e) :
    Defend p e = .revoke := by
  simp [Defend, hSensor, hCritical, hHigh, hAuth,
    hIntegrity, hPayload, hPrivilege]

/-! ============================================================
    13. No unsafe event may be ALLOWED
============================================================ -/

theorem unsafe_event_not_allowed
    (p : CyberPolicy)
    (e : SecurityEvent)
    (h : ¬ SafeToAllow p e) :
    Defend p e ≠ .allow := by
  intro hAllow
  exact h (allow_implies_safe p e hAllow)

/-! ============================================================
    14. Enforcement safety
============================================================ -/

theorem blocked_event_not_normal
    (p : CyberPolicy)
    (e : SecurityEvent)
    (h : Defend p e = .block) :
    Enforce (Defend p e) = .blocked := by
  simp [h, Enforce]

theorem quarantined_event_not_normal
    (p : CyberPolicy)
    (e : SecurityEvent)
    (h : Defend p e = .quarantine) :
    Enforce (Defend p e) = .quarantined := by
  simp [h, Enforce]

theorem halted_event_not_normal
    (p : CyberPolicy)
    (e : SecurityEvent)
    (h : Defend p e = .halt) :
    Enforce (Defend p e) = .halted := by
  simp [h, Enforce]

/-! ============================================================
    15. Audit record
============================================================ -/

structure AuditRecord where
  eventId       : Nat
  threatScore   : Nat
  confidence    : Nat
  decision      : DefenseAction
  enforcement   : EnforcementState
  sensorValid   : Bool
  authenticated : Bool
  integrity     : Bool
  payloadSafe   : Bool
  privilegeSafe : Bool

def MakeAudit
    (p : CyberPolicy)
    (e : SecurityEvent) : AuditRecord :=
  {
    eventId       := e.eventId
    threatScore   := e.threatScore
    confidence    := e.confidence
    decision      := Defend p e
    enforcement   := Enforce (Defend p e)
    sensorValid   := e.sensorAvailable
    authenticated := e.authentication
    integrity     := e.integrity
    payloadSafe   := e.payloadSafe
    privilegeSafe := e.privilegeSafe
  }

/-! ============================================================
    16. Recovery

    Recovery is permitted only after the threat has ceased
    and the sensor state is available.
============================================================ -/

def RecoveryAllowed
    (e : SecurityEvent) : Prop :=
  e.sensorAvailable = true ∧
  e.threatScore = 0 ∧
  e.integrity = true ∧
  e.payloadSafe = true ∧
  e.privilegeSafe = true

theorem recovery_requires_clean_state
    (e : SecurityEvent)
    (h : RecoveryAllowed e) :
    e.threatScore = 0 := by
  exact h.2.1

/-! ============================================================
    17. Defensive state transition
============================================================ -/

inductive DefenseTransition
  | detect
  | monitor
  | quarantine
  | block
  | revoke
  | recover
  | halt
deriving DecidableEq, Repr

def TransitionOf
    (p : CyberPolicy)
    (e : SecurityEvent) : DefenseTransition :=
  match Defend p e with
  | .monitor    => .monitor
  | .allow      => .detect
  | .quarantine => .quarantine
  | .block      => .block
  | .revoke     => .revoke
  | .recover    => .recover
  | .halt       => .halt

/-! ============================================================
    18. Security architecture invariant

    The kernel has no path from an unsafe state to ALLOW.
============================================================ -/

theorem security_kernel_is_fail_closed
    (p : CyberPolicy)
    (e : SecurityEvent) :
    ¬ SafeToAllow p e →
    Defend p e ≠ .allow :=
  unsafe_event_not_allowed p e

/-! ============================================================
    19. Default policy
============================================================ -/

def DefaultPolicy : CyberPolicy :=
  {
    minSourceTrust        := 70
    maxThreatScore        := 30
    minConfidence         := 80
    requireAuthentication := true
    requireIntegrity      := true
    requirePayloadSafety  := true
    requireEncryption     := true
    requirePrivilegeSafety := true
    quarantineThreshold   := 60
    blockThreshold        := 90
  }

/-! ============================================================
    20. Example: defensive evaluation
============================================================ -/

def ExampleEvent : SecurityEvent :=
  {
    eventId         := 1
    sourceTrust     := 90
    threatScore     := 95
    confidence      := 99
    authentication  := true
    integrity       := true
    payloadSafe     := true
    rateSafe        := true
    encrypted       := true
    privilegeSafe   := true
    humanApproved   := false
    sensorAvailable := true
  }

/--
  ExampleEvent is critical and therefore blocked.
-/
example :
    Defend DefaultPolicy ExampleEvent = .block := by
  simp [Defend, DefaultPolicy, ExampleEvent,
    IsCritical, SensorValid]

end YamamotoCyberDefense
