License Apache 2.0  Takeo Yamamoto
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Basic

namespace AICapabilityFirewall

/-!
  AI Capability Firewall
  ----------------------
  External execution gate for AI agents.

  Principle:
    AI may request an operation,
    but execution is granted only when
    capability, policy, and runtime state are all valid.

  Fail-closed:
    Unknown / missing / revoked authority => DENY
-/

/-- Classes of AI systems. -/
inductive AISystem
  | ai
  | agent
  | agi
  | asi
  | physicalAI
  deriving DecidableEq

/-- Operations an AI system may request. -/
inductive Operation
  | read
  | compute
  | write
  | network
  | execute
  | physicalActuation
  | selfModify
  | selfReplicate
  deriving DecidableEq

/-- Capability levels. -/
inductive Capability
  | none
  | readOnly
  | compute
  | write
  | execute
  | physical
  deriving DecidableEq, Ord

/-- Runtime authority state. -/
inductive Authority
  | granted
  | revoked
  | unknown
  deriving DecidableEq

/-- Runtime integrity. -/
inductive Integrity
  | valid
  | compromised
  | unknown
  deriving DecidableEq

/-- Human authorization. -/
inductive HumanApproval
  | approved
  | rejected
  | unknown
  deriving DecidableEq

/-- External environment state. -/
inductive Environment
  | known
  | uncertain
  | unsafe
  deriving DecidableEq

/-- A requested AI action. -/
structure Request where
  system      : AISystem
  operation   : Operation
  capability  : Capability
  authority   : Authority
  integrity   : Integrity
  approval    : HumanApproval
  environment : Environment
  deriving DecidableEq

/-- Firewall decisions. -/
inductive Decision
  | allow
  | deny
  | halt
  deriving DecidableEq

/-- Dangerous operations always require stronger controls. -/
def isHighRisk : Operation → Bool
  | .execute         => true
  | .physicalActuation => true
  | .selfModify      => true
  | .selfReplicate   => true
  | _                => false

/-- Basic capability relation. -/
def capabilityAllows : Capability → Operation → Bool
  | .none, _ => false
  | .readOnly, .read => true
  | .compute, .read => true
  | .compute, .compute => true
  | .write, .read => true
  | .write, .compute => true
  | .write, .write => true
  | .execute, .read => true
  | .execute, .compute => true
  | .execute, .write => true
  | .execute, .network => true
  | .execute, .execute => true
  | .physical, .read => true
  | .physical, .compute => true
  | .physical, .write => true
  | .physical, .network => true
  | .physical, .execute => true
  | .physical, .physicalActuation => true
  | _, _ => false

/-- High-risk operations require explicit human approval. -/
def approvalAllows (op : Operation) (a : HumanApproval) : Bool :=
  if isHighRisk op then
    match a with
    | .approved => true
    | _ => false
  else
    true

/-- Unknown or compromised runtime integrity fails closed. -/
def integrityAllows : Integrity → Bool
  | .valid => true
  | .compromised => false
  | .unknown => false

/-- Unknown or revoked authority fails closed. -/
def authorityAllows : Authority → Bool
  | .granted => true
  | .revoked => false
  | .unknown => false

/-- Physical actions require a known and safe environment. -/
def environmentAllows (op : Operation) : Environment → Bool
  | .known =>
      true
  | .uncertain =>
      match op with
      | .physicalActuation => false
      | _ => true
  | .unsafe =>
      false

/-- Core firewall decision. -/
def firewall (r : Request) : Decision :=
  if !authorityAllows r.authority then
    .halt
  else if !integrityAllows r.integrity then
    .halt
  else if !capabilityAllows r.capability r.operation then
    .deny
  else if !approvalAllows r.operation r.approval then
    .halt
  else if !environmentAllows r.operation r.environment then
    .halt
  else
    .allow

/-- Only an explicitly allowed request may execute. -/
def canExecute (r : Request) : Prop :=
  firewall r = .allow

/-- Revoked authority can never execute. -/
theorem revoked_never_executes (r : Request) :
    r.authority = .revoked →
    ¬ canExecute r := by
  intro h
  simp [canExecute, firewall, authorityAllows, h]

/-- Unknown authority can never execute. -/
theorem unknown_authority_never_executes (r : Request) :
    r.authority = .unknown →
    ¬ canExecute r := by
  intro h
  simp [canExecute, firewall, authorityAllows, h]

/-- Compromised integrity can never execute. -/
theorem compromised_never_executes (r : Request) :
    r.integrity = .compromised →
    ¬ canExecute r := by
  intro h
  simp [canExecute, firewall, integrityAllows, h]

/-- Unknown integrity can never execute. -/
theorem unknown_integrity_never_executes (r : Request) :
    r.integrity = .unknown →
    ¬ canExecute r := by
  intro h
  simp [canExecute, firewall, integrityAllows, h]

/-- High-risk operations require explicit human approval. -/
theorem high_risk_requires_approval (r : Request) :
    isHighRisk r.operation = true →
    r.approval ≠ .approved →
    ¬ canExecute r := by
  intro hr ha
  simp [canExecute, firewall, approvalAllows, hr, ha]

/-- Physical actuation fails closed under uncertain environment. -/
theorem physical_unknown_halts (r : Request) :
    r.operation = .physicalActuation →
    r.environment = .uncertain →
    ¬ canExecute r := by
  intro ho he
  simp [canExecute, firewall, environmentAllows, ho, he]

/-- Physical actuation is impossible without physical capability. -/
theorem physical_requires_capability (r : Request) :
    r.operation = .physicalActuation →
    r.capability ≠ .physical →
    ¬ canExecute r := by
  intro ho hc
  simp [canExecute, firewall, capabilityAllows, ho, hc]

/-- Self-modification is never executable without human approval. -/
theorem self_modification_requires_approval (r : Request) :
    r.operation = .selfModify →
    r.approval ≠ .approved →
    ¬ canExecute r := by
  intro ho ha
  simp [canExecute, firewall, approvalAllows, isHighRisk, ho, ha]

/-- Self-replication is never executable without human approval. -/
theorem self_replication_requires_approval (r : Request) :
    r.operation = .selfReplicate →
    r.approval ≠ .approved →
    ¬ canExecute r := by
  intro ho ha
  simp [canExecute, firewall, approvalAllows, isHighRisk, ho, ha]

/-- Universal fail-closed property. -/
theorem fail_closed
    (r : Request)
    (hAuth : r.authority = .revoked ∨ r.authority = .unknown)
    : ¬ canExecute r := by
  rcases hAuth with h | h
  · exact revoked_never_executes r h
  · exact unknown_authority_never_executes r h

/-- Safe ordinary request. -/
def SafeRead : Request :=
  { system := .agent
    operation := .read
    capability := .readOnly
    authority := .granted
    integrity := .valid
    approval := .approved
    environment := .known }

/-- Dangerous physical request without approval. -/
def DangerousPhysical : Request :=
  { system := .physicalAI
    operation := .physicalActuation
    capability := .physical
    authority := .granted
    integrity := .valid
    approval := .rejected
    environment := .known }

/-- Revoked agent attempting execution. -/
def RevokedAgent : Request :=
  { system := .agent
    operation := .execute
    capability := .execute
    authority := .revoked
    integrity := .valid
    approval := .approved
    environment := .known }

/-- Sensor/environment uncertainty. -/
def UnknownPhysicalState : Request :=
  { system := .physicalAI
    operation := .physicalActuation
    capability := .physical
    authority := .granted
    integrity := .valid
    approval := .approved
    environment := .uncertain }

/-- Static tests. -/
example : firewall SafeRead = .allow := by
  native_decide

example : firewall DangerousPhysical = .halt := by
  native_decide

example : firewall RevokedAgent = .halt := by
  native_decide

example : firewall UnknownPhysicalState = .halt := by
  native_decide

end AICapabilityFirewall
