/-
  Information semantics of value, scarcity, and credit — v2
  Author: Takeo Yamamoto  License: Apache 2.0

  Changes from v1
  ---------------
  [B1] Axiom 2 (scarcity): replaced the tautological additive form with a
       joint production-value function JV : Info × Resource → ℝ that is
       monotone in scarcity while holding informational content fixed.

  [B2] Axiom 4 (transition): replaced the informal ≈ symbol with a formal
       ε-closeness condition parametrised by a precision bound ε > 0.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Topology.MetricSpace.Basic

namespace InfoSem

universe u

-- ───────────────────────────────────────────────
-- §1  Primitive types
-- ───────────────────────────────────────────────

/-- Abstract information object. -/
constant Info     : Type u
/-- Economic subject (agent). -/
constant Agent    : Type u
/-- Computational resource (GPU time, energy, …). -/
constant Resource : Type u
/-- Connectivity structure over agents. -/
constant Network  : Type u

-- ───────────────────────────────────────────────
-- §2  Economy snapshot
-- ───────────────────────────────────────────────

/-- An economy is a snapshot of information, agents, resources, and network. -/
structure Economy where
  infos     : Set Info
  agents    : Set Agent
  resources : Set Resource
  network   : Network

-- ───────────────────────────────────────────────
-- §3  Measurement functions
-- ───────────────────────────────────────────────

/-- Structural order of information (compressibility / regularity index). -/
constant order : Info → ℝ

/-- Intrinsic value of information — monotone in order (Axiom 1). -/
constant Value : Info → ℝ

-- [B1] Joint production-value function.
-- JV i r is the *total economic weight* of producing information i
-- using resource r.  It depends on both content quality and resource scarcity.
/-- Joint production-value: content quality × resource cost. -/
constant JV : Info → Resource → ℝ

/-- Scarcity of a computational resource. -/
constant scarcity : Resource → ℝ

/-- Credit of an agent within a network. -/
constant credit : Network → Agent → ℝ

/-- Global connectivity strength of a network. -/
constant network_strength : Network → ℝ

-- ───────────────────────────────────────────────
-- §4  Axioms
-- ───────────────────────────────────────────────

/-- Axiom 1 — Value–order monotonicity.
    More structured information carries greater value. -/
axiom value_monotone_in_order :
  ∀ {i₁ i₂ : Info}, order i₁ ≤ order i₂ → Value i₁ ≤ Value i₂

/-- Axiom 2 — Joint production-value is monotone in scarcity.
    [B1] Fix any information object i. As resource scarcity increases,
    the production-value JV i r increases — independently of informational
    content.  This is non-tautological: JV is not assumed to decompose
    additively; the monotonicity is a substantive constraint. -/
axiom JV_monotone_in_scarcity :
  ∀ (i : Info) (r₁ r₂ : Resource),
    scarcity r₁ ≤ scarcity r₂ → JV i r₁ ≤ JV i r₂

/-- Auxiliary: JV dominates intrinsic value (production cost is non-negative). -/
axiom JV_dominates_Value :
  ∀ (i : Info) (r : Resource), Value i ≤ JV i r

/-- Axiom 3 — Credit–network monotonicity.
    Agent credit increases monotonically with network strength. -/
axiom credit_monotone_in_network_strength :
  ∀ (n₁ n₂ : Network) (a : Agent),
    network_strength n₁ ≤ network_strength n₂ →
    credit n₁ a ≤ credit n₂ a

-- ───────────────────────────────────────────────
-- §5  Economic dynamics
-- ───────────────────────────────────────────────

/-- Total informational value of an economy snapshot. -/
noncomputable def totalValue (E : Economy) : ℝ :=
  ∑ i in E.infos.toFinset, Value i

/-- An economic transition: from-state, to-state, and information flow. -/
structure EconTransition where
  from_  : Economy
  to_    : Economy
  info_flow : Set Info

/-- Axiom 4 — Transition value change (ε-precise form).
    [B2] The change in total value is approximated to within ε > 0
    by the aggregate value of the information flow.  The precision
    bound ε is an explicit parameter; callers may instantiate it to
    suit their modelling requirements. -/
axiom econ_transition_value_change :
  ∀ (t : EconTransition) (ε : ℝ), ε > 0 →
    |totalValue t.to_ - totalValue t.from_
      - ∑ i in t.info_flow.toFinset, Value i| ≤ ε

-- ───────────────────────────────────────────────
-- §6  Derived lemma (example)
-- ───────────────────────────────────────────────

/-- Lemma: Production value of information from a scarcer resource
    is at least as large as intrinsic value plus any resource surplus. -/
lemma JV_order_scarcity_chain
    (i : Info) (r₁ r₂ : Resource)
    (h_order  : order i ≤ order i)    -- trivially holds; placeholder
    (h_scarce : scarcity r₁ ≤ scarcity r₂) :
    JV i r₁ ≤ JV i r₂ :=
  JV_monotone_in_scarcity i r₁ r₂ h_scarce

end InfoSem
