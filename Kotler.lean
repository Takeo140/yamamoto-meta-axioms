-- Kotler's Marketing Theory: Formal Lean 4 Specification
-- Philip Kotler (Marketing Management, 1967–2022) formalized under F-Theory A1--A4

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.List.Basic
import Mathlib.Order.Defs

/-!
# Kotler's Marketing Theory

## Ontology
- `Segment`          : market segment (STP — S)
- `TargetStrategy`   : targeting decision (STP — T)
- `PositioningAxis`  : value proposition axes (STP — P)
- `MarketingMix`     : 4P / 7P
- `ProductLifeCycle` : PLC stages
- `BuyingProcess`    : consumer decision journey (5 stages)
- `CLV`              : Customer Lifetime Value

## F-Theory mapping
- A1 (Extremum)   : firm maximizes CLV / market share
- A2 (Topology)   : STP defines the competitive space; PLC is a closed ordered set
- A3 (Consistency): positioning must be unique and credible (no contradictions)
- A4 (Hierarchy)  : Market → Segment → Target → Marketing Mix → CLV
-/

-- ============================================================
-- 1. Market Segmentation (STP — S)
-- ============================================================

/-- Four bases for segmentation -/
inductive SegmentBase : Type where
  | Geographic    : SegmentBase
  | Demographic   : SegmentBase
  | Psychographic : SegmentBase
  | Behavioral    : SegmentBase
  deriving DecidableEq, Repr

/-- A market segment is characterised by a base and a measurable size ∈ ℝ≥0 -/
structure Segment where
  base        : SegmentBase
  size        : ℝ
  h_size      : 0 ≤ size
  growthRate  : ℝ          -- annual growth rate (can be negative)
  deriving Repr

/-- Segment attractiveness = size × (1 + growthRate) (A1: choose maximal) -/
noncomputable def segmentAttractiveness (s : Segment) : ℝ :=
  s.size * (1 + s.growthRate)

/-- If growth rate ≥ −1 then attractiveness ≥ 0 -/
theorem attractiveness_nonneg (s : Segment) (hg : -1 ≤ s.growthRate) :
    0 ≤ segmentAttractiveness s := by
  simp [segmentAttractiveness]
  apply mul_nonneg s.h_size
  linarith

-- ============================================================
-- 2. Targeting (STP — T)
-- ============================================================

/-- Targeting strategy -/
inductive TargetStrategy : Type where
  | Undifferentiated  : TargetStrategy   -- mass marketing
  | Differentiated    : TargetStrategy   -- multiple segments
  | Concentrated      : TargetStrategy   -- single segment (niche)
  | Micromarketing    : TargetStrategy   -- individual / local
  deriving DecidableEq, Repr

/-- Number of segments served by each strategy (lower bound) -/
def minSegmentsServed : TargetStrategy → ℕ
  | TargetStrategy.Undifferentiated => 1
  | TargetStrategy.Differentiated   => 2
  | TargetStrategy.Concentrated     => 1
  | TargetStrategy.Micromarketing   => 1

-- ============================================================
-- 3. Positioning (STP — P)
-- ============================================================

/-- Positioning axes (value proposition dimensions) -/
inductive PositioningAxis : Type where
  | Quality       : PositioningAxis
  | Price         : PositioningAxis
  | Innovation    : PositioningAxis
  | Service       : PositioningAxis
  | Sustainability: PositioningAxis
  deriving DecidableEq, Repr

/-- A positioning statement: primary axis + claimed relative score ∈ (0,1] -/
structure Positioning where
  primaryAxis : PositioningAxis
  score       : ℝ
  h_pos       : 0 < score
  h_le        : score ≤ 1
  deriving Repr

/-- A3: Two brands cannot claim identical positioning on the same axis -/
def positioningConflict (p q : Positioning) : Prop :=
  p.primaryAxis = q.primaryAxis ∧ p.score = q.score

theorem distinct_positioning_no_conflict
    (p q : Positioning) (h : p.primaryAxis ≠ q.primaryAxis) :
    ¬ positioningConflict p q := by
  intro ⟨heq, _⟩
  exact h heq

-- ============================================================
-- 4. Marketing Mix — 4P / 7P (A4: hierarchical levers)
-- ============================================================

/-- Product levels (Kotler's three-level model) -/
inductive ProductLevel : Type where
  | Core        : ProductLevel   -- core benefit
  | Actual      : ProductLevel   -- brand, quality, features, packaging
  | Augmented   : ProductLevel   -- after-sales, warranty, delivery
  deriving DecidableEq, Repr

/-- Pricing strategy -/
inductive PricingStrategy : Type where
  | CostPlus          : PricingStrategy
  | CompetitionBased  : PricingStrategy
  | ValueBased        : PricingStrategy
  | Skimming          : PricingStrategy
  | Penetration       : PricingStrategy
  deriving DecidableEq, Repr

/-- Distribution channel -/
inductive Channel : Type where
  | Direct    : Channel   -- manufacturer → consumer
  | Retailer  : Channel   -- manufacturer → retailer → consumer
  | Wholesale : Channel   -- manufacturer → wholesaler → retailer → consumer
  | Digital   : Channel
  deriving DecidableEq, Repr

/-- Promotion mix elements -/
inductive PromotionElement : Type where
  | Advertising      : PromotionElement
  | SalesPromotion   : PromotionElement
  | PublicRelations  : PromotionElement
  | PersonalSelling  : PromotionElement
  | DirectMarketing  : PromotionElement
  | DigitalMarketing : PromotionElement
  deriving DecidableEq, Repr

-- Extended 7P (services marketing)
/-- People, Process, Physical Evidence -/
structure ServiceExtension where
  hasDedicatedStaff    : Bool
  hasStandardProcess   : Bool
  hasPhysicalEvidence  : Bool

/-- Full 7P Marketing Mix -/
structure MarketingMix where
  -- 4P
  productLevel   : ProductLevel
  pricingStrat   : PricingStrategy
  channel        : Channel
  promotionMix   : List PromotionElement
  -- 7P extensions
  serviceExt     : ServiceExtension

/-- A valid 4P mix has at least one promotion element -/
def validMix (m : MarketingMix) : Prop :=
  m.promotionMix.length ≥ 1

-- ============================================================
-- 5. Product Life Cycle — PLC (A2: closed ordered set)
-- ============================================================

/-- PLC stages -/
inductive PLCStage : Type where
  | Introduction : PLCStage
  | Growth       : PLCStage
  | Maturity     : PLCStage
  | Decline      : PLCStage
  deriving DecidableEq, Repr

/-- Natural ordering: Introduction < Growth < Maturity < Decline -/
def PLCStage.toNat : PLCStage → ℕ
  | PLCStage.Introduction => 0
  | PLCStage.Growth       => 1
  | PLCStage.Maturity     => 2
  | PLCStage.Decline      => 3

instance : LE PLCStage where
  le a b := a.toNat ≤ b.toNat

/-- PLC is linearly ordered -/
theorem plc_total_order (a b : PLCStage) :
    a ≤ b ∨ b ≤ a := by
  simp [LE.le, PLCStage.toNat]
  omega

/-- Introduction precedes Decline -/
theorem intro_before_decline :
    PLCStage.Introduction ≤ PLCStage.Decline := by
  simp [LE.le, PLCStage.toNat]

/-- Recommended cash investment is highest in Growth stage (A1) -/
def recommendedInvestment : PLCStage → ℕ
  | PLCStage.Introduction => 2   -- build awareness
  | PLCStage.Growth       => 3   -- maximize share
  | PLCStage.Maturity     => 1   -- defend / harvest
  | PLCStage.Decline      => 0   -- divest or maintain minimally

-- ============================================================
-- 6. Consumer Buying Process (5 stages)
-- ============================================================

/-- Kotler's five-stage consumer decision process -/
inductive BuyingStage : Type where
  | NeedRecognition       : BuyingStage
  | InformationSearch     : BuyingStage
  | EvaluationAlternatives: BuyingStage
  | PurchaseDecision      : BuyingStage
  | PostPurchaseBehavior  : BuyingStage
  deriving DecidableEq, Repr

def BuyingStage.toNat : BuyingStage → ℕ
  | BuyingStage.NeedRecognition        => 0
  | BuyingStage.InformationSearch      => 1
  | BuyingStage.EvaluationAlternatives => 2
  | BuyingStage.PurchaseDecision       => 3
  | BuyingStage.PostPurchaseBehavior   => 4

/-- Process is strictly sequential: purchase follows need recognition -/
theorem need_before_purchase :
    BuyingStage.NeedRecognition.toNat < BuyingStage.PurchaseDecision.toNat := by
  simp [BuyingStage.toNat]

/-- Post-purchase behavior is the final stage -/
theorem post_purchase_is_last (s : BuyingStage) :
    s.toNat ≤ BuyingStage.PostPurchaseBehavior.toNat := by
  cases s <;> simp [BuyingStage.toNat]

-- ============================================================
-- 7. Customer Lifetime Value — CLV (A1: maximize)
-- ============================================================

/-- CLV inputs -/
structure CLVInputs where
  annualRevenue    : ℝ           -- average annual revenue per customer
  annualCost       : ℝ           -- cost to serve per year
  retentionRate    : ℝ           -- r ∈ [0,1)
  discountRate     : ℝ           -- d > 0
  h_rev_pos        : 0 ≤ annualRevenue
  h_ret_lo         : 0 ≤ retentionRate
  h_ret_hi         : retentionRate < 1
  h_disc_pos       : 0 < discountRate

/-- CLV = (revenue − cost) × r / (1 + d − r)  [simplified perpetuity model] -/
noncomputable def clv (c : CLVInputs) : ℝ :=
  let margin := c.annualRevenue - c.annualCost
  let denom  := 1 + c.discountRate - c.retentionRate
  margin * (c.retentionRate / denom)

/-- Denominator is strictly positive -/
theorem clv_denom_pos (c : CLVInputs) :
    0 < 1 + c.discountRate - c.retentionRate := by
  linarith [c.h_ret_hi, c.h_disc_pos]

/-- Helper: r / (1 + d − r) is monotone increasing in r
    Proof: cross-multiply ⟹ r(1+d) ≤ r'(1+d) ⟹ r ≤ r'  (since d > 0) -/
private lemma retention_ratio_mono
    {r r' d : ℝ}
    (hr     : r ≤ r')
    (hr_hi  : r  < 1)
    (hr'_hi : r' < 1)
    (hd     : 0 < d) :
    r / (1 + d - r) ≤ r' / (1 + d - r') := by
  have hd1 : 0 < 1 + d - r  := by linarith
  have hd2 : 0 < 1 + d - r' := by linarith
  rw [div_le_div_iff hd1 hd2]
  nlinarith

/-- A1: CLV increases with retention rate (monotonicity, fully proved) -/
theorem clv_increases_with_retention
    (c : CLVInputs)
    (h_margin : 0 < c.annualRevenue - c.annualCost)
    (r' : ℝ) (hr'_lo : c.retentionRate ≤ r') (hr'_hi : r' < 1) :
    clv c ≤ clv { c with
      retentionRate := r'
      h_ret_lo      := le_trans c.h_ret_lo hr'_lo
      h_ret_hi      := hr'_hi } := by
  simp only [clv]
  apply mul_le_mul_of_nonneg_left _ (le_of_lt h_margin)
  exact retention_ratio_mono hr'_lo c.h_ret_hi hr'_hi c.h_disc_pos

-- ============================================================
-- 8. STP + Mix Integration (A4: hierarchy)
-- ============================================================

/-- A complete market offer: STP + Mix + PLC stage -/
structure MarketOffer where
  segment     : Segment
  targeting   : TargetStrategy
  positioning : Positioning
  mix         : MarketingMix
  plcStage    : PLCStage

/-- A4: marketing investment should be consistent with PLC stage -/
def plcConsistentInvestment (o : MarketOffer) : Prop :=
  match o.plcStage with
  | PLCStage.Introduction => o.mix.promotionMix.length ≥ 2  -- heavy launch spend
  | PLCStage.Growth       => o.mix.promotionMix.length ≥ 2
  | PLCStage.Maturity     => o.mix.promotionMix.length ≥ 1
  | PLCStage.Decline      => True                           -- no constraint

/-- Any MarketOffer in Decline stage trivially satisfies investment consistency -/
theorem decline_always_consistent (o : MarketOffer)
    (hd : o.plcStage = PLCStage.Decline) :
    plcConsistentInvestment o := by
  simp [plcConsistentInvestment, hd]
