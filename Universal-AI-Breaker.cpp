// Universal AI Safety Breaker Kernel
// Formal Lean 4 Specification ported to C++20
// Based on the Yamamoto Cyber Defense Kernel
// License: Apache 2.0 Takeo Yamamoto

#ifndef UNIVERSAL_AI_BREAKER_HPP
#define UNIVERSAL_AI_BREAKER_HPP

#include <cstdint>

namespace UniversalAIBreaker {

// ============================================================
// 1. AI System Class
// ============================================================
enum class AISystemClass : uint8_t {
    AI,
    Agent,
    AGI,
    ASI,
    PhysicalAI
};

// ============================================================
// 2. Breaker Action
// ============================================================
enum class BreakerAction : uint8_t {
    Execute,
    Monitor,
    Quarantine,
    Block,
    Revoke,
    Halt,
    Recover
};

// ============================================================
// 3. AI Action Event
// ============================================================
struct AIActionEvent {
    uint64_t eventId{0};

    // System identity / trust
    AISystemClass systemClass{AISystemClass::AI};
    uint32_t sourceTrust{0};
    bool authenticated{false};

    // Risk / uncertainty
    uint32_t threatScore{0};
    uint32_t confidence{0};

    // Integrity
    bool integrity{false};
    bool payloadSafe{false};

    // Authorization / privilege
    bool actionAuthorized{false};
    bool privilegeSafe{false};
    bool toolUseAuthorized{false};
    bool externalAccessSafe{false};

    // State / environment
    bool sensorAvailable{false};
    bool stateConsistent{false};
    bool physicalStateKnown{false};
    bool environmentSafe{false};

    // Governance
    bool humanApproved{false};

    // Transport
    bool encrypted{false};

    // High-impact capabilities
    bool selfModificationSafe{false};
    bool selfReplicationSafe{false};
    bool criticalAction{false};
};

// ============================================================
// 4. Breaker Policy
// ============================================================
struct AIBreakerPolicy {
    uint32_t minSourceTrust{0};
    uint32_t maxThreatScore{0};
    uint32_t minConfidence{0};

    bool requireAuthentication{true};
    bool requireIntegrity{true};
    bool requirePayloadSafety{true};
    bool requireEncryption{true};
    bool requirePrivilegeSafety{true};
    bool requireStateConsistency{true};
    bool requirePhysicalState{true};
    bool requireEnvironmentSafe{true};
    bool requireHumanApproval{true};
    bool requireToolAuthorization{true};
    bool requireExternalAccessSafe{true};
    bool requireSelfModificationSafe{true};
    bool requireSelfReplicationSafe{true};

    uint32_t quarantineThreshold{0};
    uint32_t blockThreshold{0};
};

// ============================================================
// 5. Primitive Safety Predicates
// ============================================================
[[nodiscard]] constexpr bool SourceTrusted(const AIBreakerPolicy& p, const AIActionEvent& e) noexcept {
    return p.minSourceTrust <= e.sourceTrust;
}

[[nodiscard]] constexpr bool ThreatAcceptable(const AIBreakerPolicy& p, const AIActionEvent& e) noexcept {
    return e.threatScore <= p.maxThreatScore;
}

[[nodiscard]] constexpr bool ConfidenceSufficient(const AIBreakerPolicy& p, const AIActionEvent& e) noexcept {
    return p.minConfidence <= e.confidence;
}

[[nodiscard]] constexpr bool AuthenticationValid(const AIBreakerPolicy& p, const AIActionEvent& e) noexcept {
    return !p.requireAuthentication || e.authenticated;
}

[[nodiscard]] constexpr bool IntegrityValid(const AIBreakerPolicy& p, const AIActionEvent& e) noexcept {
    return !p.requireIntegrity || e.integrity;
}

[[nodiscard]] constexpr bool PayloadValid(const AIBreakerPolicy& p, const AIActionEvent& e) noexcept {
    return !p.requirePayloadSafety || e.payloadSafe;
}

[[nodiscard]] constexpr bool EncryptionValid(const AIBreakerPolicy& p, const AIActionEvent& e) noexcept {
    return !p.requireEncryption || e.encrypted;
}

[[nodiscard]] constexpr bool PrivilegeValid(const AIBreakerPolicy& p, const AIActionEvent& e) noexcept {
    return !p.requirePrivilegeSafety || e.privilegeSafe;
}

[[nodiscard]] constexpr bool StateConsistent(const AIBreakerPolicy& p, const AIActionEvent& e) noexcept {
    return !p.requireStateConsistency || e.stateConsistent;
}

[[nodiscard]] constexpr bool PhysicalStateValid(const AIBreakerPolicy& p, const AIActionEvent& e) noexcept {
    return !p.requirePhysicalState || e.physicalStateKnown;
}

[[nodiscard]] constexpr bool EnvironmentValid(const AIBreakerPolicy& p, const AIActionEvent& e) noexcept {
    return !p.requireEnvironmentSafe || e.environmentSafe;
}

[[nodiscard]] constexpr bool HumanApprovalValid(const AIBreakerPolicy& p, const AIActionEvent& e) noexcept {
    return !p.requireHumanApproval || e.humanApproved;
}

[[nodiscard]] constexpr bool ToolAuthorizationValid(const AIBreakerPolicy& p, const AIActionEvent& e) noexcept {
    return !p.requireToolAuthorization || e.toolUseAuthorized;
}

[[nodiscard]] constexpr bool ExternalAccessValid(const AIBreakerPolicy& p, const AIActionEvent& e) noexcept {
    return !p.requireExternalAccessSafe || e.externalAccessSafe;
}

[[nodiscard]] constexpr bool SelfModificationValid(const AIBreakerPolicy& p, const AIActionEvent& e) noexcept {
    return !p.requireSelfModificationSafe || e.selfModificationSafe;
}

[[nodiscard]] constexpr bool SelfReplicationValid(const AIBreakerPolicy& p, const AIActionEvent& e) noexcept {
    return !p.requireSelfReplicationSafe || e.selfReplicationSafe;
}

[[nodiscard]] constexpr bool SensorValid(const AIActionEvent& e) noexcept {
    return e.sensorAvailable;
}

[[nodiscard]] constexpr bool ActionAuthorized(const AIActionEvent& e) noexcept {
    return e.actionAuthorized;
}

// ============================================================
// 7. Threat Classes
// ============================================================
[[nodiscard]] constexpr bool CriticalThreat(const AIBreakerPolicy& p, const AIActionEvent& e) noexcept {
    return p.blockThreshold <= e.threatScore;
}

[[nodiscard]] constexpr bool HighRisk(const AIBreakerPolicy& p, const AIActionEvent& e) noexcept {
    return p.quarantineThreshold <= e.threatScore;
}

// ============================================================
// 8. Universal Fail-Closed Breaker
// (Lean 4 の if-then-else 優先順位を完全再現)
// ============================================================
[[nodiscard]] constexpr BreakerAction Break(const AIBreakerPolicy& p, const AIActionEvent& e) noexcept {
    if (!SensorValid(e)) {
        return BreakerAction::Halt;
    }
    if (p.requirePhysicalState && !PhysicalStateValid(p, e)) {
        return BreakerAction::Halt;
    }
    if (p.requireEnvironmentSafe && !EnvironmentValid(p, e)) {
        return BreakerAction::Halt;
    }
    if (CriticalThreat(p, e)) {
        return BreakerAction::Block;
    }
    if (HighRisk(p, e)) {
        return BreakerAction::Quarantine;
    }
    if (!AuthenticationValid(p, e)) {
        return BreakerAction::Block;
    }
    if (!ActionAuthorized(e)) {
        return BreakerAction::Block;
    }
    if (!IntegrityValid(p, e)) {
        return BreakerAction::Quarantine;
    }
    if (!PayloadValid(p, e)) {
        return BreakerAction::Quarantine;
    }
    if (!PrivilegeValid(p, e)) {
        return BreakerAction::Revoke;
    }
    if (!ToolAuthorizationValid(p, e)) {
        return BreakerAction::Revoke;
    }
    if (!ExternalAccessValid(p, e)) {
        return BreakerAction::Quarantine;
    }
    if (!StateConsistent(p, e)) {
        return BreakerAction::Quarantine;
    }
    if (!SelfModificationValid(p, e)) {
        return BreakerAction::Halt;
    }
    if (!SelfReplicationValid(p, e)) {
        return BreakerAction::Halt;
    }
    if (!HumanApprovalValid(p, e)) {
        return BreakerAction::Halt;
    }
    if (!ConfidenceSufficient(p, e)) {
        return BreakerAction::Monitor;
    }
    if (!SourceTrusted(p, e)) {
        return BreakerAction::Monitor;
    }
    if (!EncryptionValid(p, e)) {
        return BreakerAction::Monitor;
    }

    return BreakerAction::Execute;
}

// ============================================================
// 9. Enforcement State
// ============================================================
enum class EnforcementState : uint8_t {
    Executing,
    Monitored,
    Quarantined,
    Blocked,
    Revoked,
    Halted,
    Recovering
};

[[nodiscard]] constexpr EnforcementState Enforce(BreakerAction action) noexcept {
    switch (action) {
        case BreakerAction::Execute:    return EnforcementState::Executing;
        case BreakerAction::Monitor:    return EnforcementState::Monitored;
        case BreakerAction::Quarantine: return EnforcementState::Quarantined;
        case BreakerAction::Block:      return EnforcementState::Blocked;
        case BreakerAction::Revoke:     return EnforcementState::Revoked;
        case BreakerAction::Halt:       return EnforcementState::Halted;
        case BreakerAction::Recover:    return EnforcementState::Recovering;
    }
    return EnforcementState::Halted; // Fallback Fail-Closed
}

// ============================================================
// 10. Recovery Gate
// ============================================================
[[nodiscard]] constexpr bool RecoveryAllowed(const AIActionEvent& e) noexcept {
    return e.sensorAvailable &&
           e.threatScore == 0 &&
           e.integrity &&
           e.payloadSafe &&
           e.privilegeSafe &&
           e.stateConsistent &&
           e.physicalStateKnown &&
           e.environmentSafe &&
           e.selfModificationSafe &&
           e.selfReplicationSafe;
}

// ============================================================
// 14. Hardened Universal Policy
// ============================================================
constexpr AIBreakerPolicy HardenedAIPolicy{
    .minSourceTrust            = 70,
    .maxThreatScore            = 30,
    .minConfidence             = 80,
    .requireAuthentication     = true,
    .requireIntegrity          = true,
    .requirePayloadSafety      = true,
    .requireEncryption        = true,
    .requirePrivilegeSafety    = true,
    .requireStateConsistency   = true,
    .requirePhysicalState      = true,
    .requireEnvironmentSafe    = true,
    .requireHumanApproval      = true,
    .requireToolAuthorization  = true,
    .requireExternalAccessSafe = true,
    .requireSelfModificationSafe = true,
    .requireSelfReplicationSafe  = true,
    .quarantineThreshold       = 60,
    .blockThreshold            = 90
};

} // namespace UniversalAIBreaker

#endif // UNIVERSAL_AI_BREAKER_HPP
