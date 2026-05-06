-- Drucker's Management Theory: Formal Lean 4 Specification
-- Peter F. Drucker (1954–2001) formalized under F-Theory A1--A4

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.List.Basic
import Mathlib.Order.Defs

/-!
# Drucker's Management Theory

## Ontology
- `Objective`          : MBO — measurable goal with deadline
- `KnowledgeWorker`    : self-managing contributor
- `EffectivePractice`  : five habits of the effective executive
- `InnovationSource`   : seven sources of innovation
- `DeadlySin`          : five deadly sins of management
- `Organization`       : purposive social institution
- `DecisionProcess`    : Drucker's rational decision steps

## F-Theory mapping
- A1 (Extremum)   : management maximizes organizational effectiveness
- A2 (Topology)   : objective space and innovation sources form closed sets
- A3 (Consistency): MBO requires congruence between individual and org objectives
- A4 (Hierarchy)  : Society ⊃ Organization ⊃ Manager ⊃ Knowledge Worker ⊃ Objective
-/

-- ============================================================
-- 1. Management by Objectives — MBO (A1 + A3)
-- ============================================================

/-- An objective must be specific, measurable, time-bound -/
structure Objective where
  description   : String
  targetValue   : ℝ           -- quantified target
  currentValue  : ℝ           -- baseline at planning time
  deadlineDays  : ℕ           -- days until due
  h_target_pos  : 0 < targetValue
  h_deadline    : 0 < deadlineDays
  deriving Repr

/-- Achievement ratio ∈ [0, ∞) — 1.0 means fully met -/
noncomputable def achievementRatio (o : Objective) : ℝ :=
  o.currentValue / o.targetValue

/-- Gap to close -/
noncomputable def objectiveGap (o : Objective) : ℝ :=
  o.targetValue - o.currentValue

/-- A3: organizational objective set is consistent iff
    no two objectives contradict (here: gaps have same sign) -/
def objectivesConsistent (os : List Objective) : Prop :=
  ∀ a b ∈ os, 0 ≤ objectiveGap a ↔ 0 ≤ objectiveGap b

/-- A1: the optimal objective is the one minimizing gap-to-deadline ratio -/
noncomputable def urgency (o : Objective) : ℝ :=
  objectiveGap o / o.deadlineDays

-- ============================================================
-- 2. Knowledge Worker (A4: hierarchy leaf)
-- ============================================================

/-- Contribution type of a knowledge worker -/
inductive ContributionType : Type where
  | DirectResults   : ContributionType   -- output, revenue, product
  | ValuesStandards : ContributionType   -- culture, ethics
  | DevelopingPeople: ContributionType   -- mentoring, succession
  deriving DecidableEq, Repr

/-- A knowledge worker is defined by autonomy + contribution type -/
structure KnowledgeWorker where
  name             : String
  contribution     : ContributionType
  selfManaged      : Bool
  continuousLearn  : Bool               -- Drucker: KW must keep learning

/-- An effective knowledge worker is self-managed and continuously learning -/
def isEffectiveKW (w : KnowledgeWorker) : Prop :=
  w.selfManaged = true ∧ w.continuousLearn = true

/-- A3: a worker who is not self-managed cannot deliver autonomous contribution -/
theorem non_self_managed_not_effective (w : KnowledgeWorker)
    (h : w.selfManaged = false) : ¬ isEffectiveKW w := by
  simp [isEffectiveKW, h]

-- ============================================================
-- 3. The Effective Executive — Five Practices (A1)
-- ============================================================

/-- Drucker's five practices of the effective executive -/
inductive EffectivePractice : Type where
  | ManageTime          : EffectivePractice  -- know where time goes
  | FocusContribution   : EffectivePractice  -- ask "what can I contribute?"
  | BuildOnStrengths    : EffectivePractice  -- staff for strength, not absence of weakness
  | FirstThingsFirst    : EffectivePractice  -- concentrate on few priorities
  | MakeEffectiveDecisions : EffectivePractice
  deriving DecidableEq, Repr

/-- All five practices are distinct -/
theorem practices_distinct :
    EffectivePractice.ManageTime       ≠ EffectivePractice.FocusContribution    ∧
    EffectivePractice.ManageTime       ≠ EffectivePractice.BuildOnStrengths     ∧
    EffectivePractice.ManageTime       ≠ EffectivePractice.FirstThingsFirst     ∧
    EffectivePractice.ManageTime       ≠ EffectivePractice.MakeEffectiveDecisions ∧
    EffectivePractice.FocusContribution ≠ EffectivePractice.BuildOnStrengths    ∧
    EffectivePractice.FocusContribution ≠ EffectivePractice.FirstThingsFirst    ∧
    EffectivePractice.FocusContribution ≠ EffectivePractice.MakeEffectiveDecisions ∧
    EffectivePractice.BuildOnStrengths ≠ EffectivePractice.FirstThingsFirst     ∧
    EffectivePractice.BuildOnStrengths ≠ EffectivePractice.MakeEffectiveDecisions ∧
    EffectivePractice.FirstThingsFirst ≠ EffectivePractice.MakeEffectiveDecisions := by
  simp

/-- An executive is effective iff they practice all five habits -/
structure Executive where
  name     : String
  practices: Finset EffectivePractice

def allPractices : Finset EffectivePractice :=
  { EffectivePractice.ManageTime,
    EffectivePractice.FocusContribution,
    EffectivePractice.BuildOnStrengths,
    EffectivePractice.FirstThingsFirst,
    EffectivePractice.MakeEffectiveDecisions }

def isEffectiveExecutive (e : Executive) : Prop :=
  allPractices ⊆ e.practices

-- ============================================================
-- 4. Innovation — Seven Sources (A2: closed set)
-- ============================================================

/-- Drucker's seven sources of innovation opportunity -/
inductive InnovationSource : Type where
  | UnexpectedOccurrence  : InnovationSource  -- unexpected success / failure
  | Incongruity           : InnovationSource  -- gap between reality and assumption
  | ProcessNeed           : InnovationSource  -- weak link in process
  | IndustryStructure     : InnovationSource  -- structural change in market
  | Demographics          : InnovationSource  -- population changes
  | ChangesInPerception   : InnovationSource  -- mood / meaning shifts
  | NewKnowledge          : InnovationSource  -- scientific or social
  deriving DecidableEq, Repr

/-- Sources are ordered by reliability (internal < external) -/
def InnovationSource.toNat : InnovationSource → ℕ
  | InnovationSource.UnexpectedOccurrence => 1  -- most reliable (internal)
  | InnovationSource.Incongruity          => 2
  | InnovationSource.ProcessNeed          => 3
  | InnovationSource.IndustryStructure    => 4
  | InnovationSource.Demographics         => 5
  | InnovationSource.ChangesInPerception  => 6
  | InnovationSource.NewKnowledge         => 7  -- least reliable (external)

instance : LE InnovationSource where
  le a b := a.toNat ≤ b.toNat

/-- Seven sources form a total order -/
theorem innovation_source_total (a b : InnovationSource) :
    a ≤ b ∨ b ≤ a := by
  simp [LE.le, InnovationSource.toNat]
  omega

/-- UnexpectedOccurrence is the most reliable source -/
theorem unexpected_most_reliable (s : InnovationSource) :
    InnovationSource.UnexpectedOccurrence ≤ s := by
  cases s <;> simp [LE.le, InnovationSource.toNat]

-- ============================================================
-- 5. Five Deadly Sins of Management (A3: prohibitions)
-- ============================================================

/-- Drucker's five deadly sins -/
inductive DeadlySin : Type where
  | Worship_High_Profit_Margins   : DeadlySin  -- kills market share
  | MispricingNewProduct          : DeadlySin  -- price what market bears, not cost+
  | CostDrivenPricing             : DeadlySin  -- vs. price-driven costing
  | SlaughterTomorrow_For_Today   : DeadlySin  -- sacrifice future for short-term EPS
  | FeedProblems_StarveOpportunity: DeadlySin  -- resource allocation failure
  deriving DecidableEq, Repr

/-- A healthy management posture avoids all five sins -/
def isHealthyManagement (sins : Finset DeadlySin) : Prop :=
  sins = ∅

/-- Committing any sin violates health -/
theorem any_sin_unhealthy (s : DeadlySin) :
    ¬ isHealthyManagement {s} := by
  simp [isHealthyManagement]

-- ============================================================
-- 6. Organization as Social Institution (A4: hierarchy)
-- ============================================================

/-- Organizational purpose dimension -/
inductive OrgPurpose : Type where
  | EconomicPerformance : OrgPurpose   -- primary (Drucker: only business justification)
  | WorkerFulfillment   : OrgPurpose   -- secondary but necessary
  | SocialResponsibility: OrgPurpose   -- tertiary — cannot override primary
  deriving DecidableEq, Repr

/-- Priority order: Economic > Worker > Social -/
def OrgPurpose.priority : OrgPurpose → ℕ
  | OrgPurpose.EconomicPerformance  => 3
  | OrgPurpose.WorkerFulfillment    => 2
  | OrgPurpose.SocialResponsibility => 1

/-- A4: Economic performance has highest priority -/
theorem economic_performance_highest (p : OrgPurpose) :
    p.priority ≤ OrgPurpose.EconomicPerformance.priority := by
  cases p <;> simp [OrgPurpose.priority]

structure Organization where
  name       : String
  objectives : List Objective
  workers    : List KnowledgeWorker
  executives : List Executive

/-- An organization is well-managed iff
    (i)  objectives are consistent, and
    (ii) all executives are effective -/
def isWellManaged (org : Organization) : Prop :=
  objectivesConsistent org.objectives ∧
  ∀ e ∈ org.executives, isEffectiveExecutive e

-- ============================================================
-- 7. Drucker's Decision Process (A1: rational extremum)
-- ============================================================

/-- Six steps of Drucker's effective decision process -/
inductive DecisionStep : Type where
  | ClassifyProblem      : DecisionStep  -- generic vs. unique
  | DefineProblem        : DecisionStep  -- what is this really about?
  | SpecifyBoundaryConditions : DecisionStep  -- what must the solution satisfy?
  | DecideRightAnswer    : DecisionStep  -- what is right (before compromise)?
  | BuildInAction        : DecisionStep  -- convert to action
  | TestValidity         : DecisionStep  -- feedback loop
  deriving DecidableEq, Repr

def DecisionStep.toNat : DecisionStep → ℕ
  | DecisionStep.ClassifyProblem           => 0
  | DecisionStep.DefineProblem             => 1
  | DecisionStep.SpecifyBoundaryConditions => 2
  | DecisionStep.DecideRightAnswer         => 3
  | DecisionStep.BuildInAction             => 4
  | DecisionStep.TestValidity              => 5

instance : LE DecisionStep where
  le a b := a.toNat ≤ b.toNat

/-- Decision process is strictly sequential -/
theorem classify_before_test :
    DecisionStep.ClassifyProblem ≤ DecisionStep.TestValidity := by
  simp [LE.le, DecisionStep.toNat]

theorem define_before_decide :
    DecisionStep.DefineProblem ≤ DecisionStep.DecideRightAnswer := by
  simp [LE.le, DecisionStep.toNat]

/-- All steps form a total order -/
theorem decision_total (a b : DecisionStep) :
    a ≤ b ∨ b ≤ a := by
  simp [LE.le, DecisionStep.toNat]
  omega

-- ============================================================
-- 8. Self-Management (A1: knowledge worker maximizes contribution)
-- ============================================================

/-- Drucker's self-management axes -/
structure SelfManagementProfile where
  knowsStrengths        : Bool
  knowsWorkStyle        : Bool   -- how do I work best?
  knowsValues           : Bool
  knowsWhereIBelong     : Bool
  knowsContribution     : Bool   -- what should my contribution be?

/-- A complete self-management profile enables full contribution -/
def completeSelfProfile (p : SelfManagementProfile) : Prop :=
  p.knowsStrengths    = true ∧
  p.knowsWorkStyle    = true ∧
  p.knowsValues       = true ∧
  p.knowsWhereIBelong = true ∧
  p.knowsContribution = true

/-- A3: Without knowing one's values, belonging cannot be determined correctly -/
theorem values_required_for_belonging (p : SelfManagementProfile)
    (h : p.knowsValues = false) : ¬ completeSelfProfile p := by
  simp [completeSelfProfile, h]

/-- A1: Only a complete profile yields maximum effectiveness -/
theorem incomplete_profile_limits_effectiveness (p : SelfManagementProfile)
    (h : p.knowsStrengths = false) : ¬ completeSelfProfile p := by
  simp [completeSelfProfile, h]

-- ============================================================
-- 9. MBO Alignment Theorem (A3: congruence)
-- ============================================================

/-- Individual and organizational objectives are aligned iff
    both point in the same direction (positive gap) -/
def aligned (individual org : Objective) : Prop :=
  (0 ≤ objectiveGap individual) ↔ (0 ≤ objectiveGap org)

/-- Alignment is reflexive -/
theorem aligned_refl (o : Objective) : aligned o o := by
  simp [aligned]

/-- Alignment is symmetric -/
theorem aligned_symm (a b : Objective) (h : aligned a b) : aligned b a := by
  simp [aligned] at *
  exact h.symm
