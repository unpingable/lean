/-
  LeanProofs.Admissibility.WitnessedReachability — adapters from the WDC paid-path spine
  into the generic reachability/refusal vocabulary.

  Custody-Class: UNRATIFIED-CANDIDATE

  Status: adapter slice. Root-imported for build coverage, but NOT a
  promoted AdmissibilityKernels surface and NOT a new WDC receipt. The point is to avoid a
  sixth reachability encoding: `PaidFrom` remains the WDC spine's path judgment, while
  `ReachabilityClosure.Reach` is the generic vocabulary used by refusal/closed-lane results.

  No classifier, no trichotomy, no revival of the retired composition-classification gate.
-/

import LeanProofs.Admissibility.ReachabilityClosure
import LeanProofs.Witnessed.Embedding

namespace LeanProofs.Admissibility.WitnessedReachability

open LeanProofs.Admissibility.ReachabilityClosure
open LeanProofs.Witnessed
open LeanProofs.Witnessed.NoFreeLift

variable {Claim : Type}

/-! ## Adapters: WDC `PaidFrom` <-> generic `Reach` -/

/-- A WDC paid path is an ordinary reachability path over the same bridge relation. -/
theorem paidFrom_to_reach {Bridge : Claim → Claim → Prop} {a b : Claim}
    (h : PaidFrom Bridge a b) : Reach Bridge a b := by
  induction h with
  | refl => exact Reach.refl
  | step _ hb ih => exact Reach.tail ih hb

/-- A generic reachability path can be read back as a WDC paid path. -/
theorem reach_to_paidFrom {Bridge : Claim → Claim → Prop} {a b : Claim}
    (h : Reach Bridge a b) : PaidFrom Bridge a b := by
  induction h with
  | refl => exact PaidFrom.refl
  | tail _ hb ih => exact PaidFrom.step ih hb

/-- The two path encodings carry the same information; callers can choose the induction
    direction they need without minting another closure relation. -/
theorem paidFrom_iff_reach {Bridge : Claim → Claim → Prop} {a b : Claim} :
    PaidFrom Bridge a b ↔ Reach Bridge a b := by
  constructor
  · exact paidFrom_to_reach
  · exact reach_to_paidFrom

/-- A closed-lane refusal blocks WDC paid paths. -/
theorem closed_lane_blocks_paidFrom {Bridge : Claim → Claim → Prop} {a b : Claim}
    (h : ClosedLaneRefusal Bridge a b) : ¬ PaidFrom Bridge a b := by
  intro hp
  exact h.refused (paidFrom_to_reach hp)

/-- If every kernel claim starts inside a closed lane and the target is outside it, WDC
    derivability is blocked. This is `no_free_lift` plus the closed-lane obstruction. -/
theorem closed_lane_blocks_lift {Kernel : Claim → Prop} {Bridge : Claim → Claim → Prop}
    {S : Claim → Prop} {dst : Claim}
    (h_closed : ClosedUnder Bridge S)
    (h_kernel : ∀ c, Kernel c → S c)
    (h_dst : ¬ S dst) : ¬ Lift Kernel Bridge dst := by
  intro hLift
  obtain ⟨c₀, hk, hp⟩ := no_free_lift hLift
  exact h_dst
    (reach_stays_in_closed (Step := Bridge) (S := S) h_closed
      (paidFrom_to_reach (Bridge := Bridge) hp) (h_kernel c₀ hk))

/-! ## Existing WDC embedding lanes: authority and freshness are separated -/

/-- The authority summand as a closed-lane candidate. -/
def AuthorityLane : Embedding.Claim → Prop := fun c => ∃ a, c = Sum.inl a

/-- The freshness summand as a closed-lane candidate. -/
def FreshnessLane : Embedding.Claim → Prop := fun c => ∃ f, c = Sum.inr f

/-- Authority is forward-closed under the existing WDC embedding bridge. In practice this is
    vacuous: no bridge leaves an authority claim at all. -/
theorem authorityLane_closed : ClosedUnder Embedding.Bridge AuthorityLane := by
  intro x y hx hb
  obtain ⟨a, rfl⟩ := hx
  cases y with
  | inl a' => exact ⟨a', rfl⟩
  | inr _ => exact hb.elim

/-- Freshness is forward-closed under the existing WDC embedding bridge. -/
theorem freshnessLane_closed : ClosedUnder Embedding.Bridge FreshnessLane := by
  intro _x _y _hx hb
  exact Embedding.bridge_both_freshness hb |>.2

/-- Authority cannot reach freshness by paid bridges; the receipt is the authority lane. -/
def authority_to_freshness_closed_lane (a : Embedding.AuthClaim) (f : Embedding.FreshClaim) :
    ClosedLaneRefusal Embedding.Bridge (Sum.inl a) (Sum.inr f) where
  lane := AuthorityLane
  closed := authorityLane_closed
  src_mem := ⟨a, rfl⟩
  dst_not_mem := by
    rintro ⟨_a, h⟩
    cases h

/-- Freshness cannot reach authority by paid bridges; the receipt is the freshness lane. -/
def freshness_to_authority_closed_lane (f : Embedding.FreshClaim) (a : Embedding.AuthClaim) :
    ClosedLaneRefusal Embedding.Bridge (Sum.inr f) (Sum.inl a) where
  lane := FreshnessLane
  closed := freshnessLane_closed
  src_mem := ⟨f, rfl⟩
  dst_not_mem := by
    rintro ⟨_f, h⟩
    cases h

/-- Closed-lane form of the existing no authority -> freshness paid-path fact. -/
theorem authority_to_freshness_refused (a : Embedding.AuthClaim) (f : Embedding.FreshClaim) :
    Refused Embedding.Bridge (Sum.inl a) (Sum.inr f) :=
  (authority_to_freshness_closed_lane a f).refused

/-- Closed-lane form of the existing no freshness -> authority paid-path fact. -/
theorem freshness_to_authority_refused (f : Embedding.FreshClaim) (a : Embedding.AuthClaim) :
    Refused Embedding.Bridge (Sum.inr f) (Sum.inl a) :=
  (freshness_to_authority_closed_lane f a).refused

/-- WDC paid paths cannot cross authority -> freshness in the existing embedding. -/
theorem no_paid_authority_to_freshness (a : Embedding.AuthClaim) (f : Embedding.FreshClaim) :
    ¬ PaidFrom Embedding.Bridge (Sum.inl a) (Sum.inr f) :=
  closed_lane_blocks_paidFrom (authority_to_freshness_closed_lane a f)

/-- WDC paid paths cannot cross freshness -> authority in the existing embedding. -/
theorem no_paid_freshness_to_authority (f : Embedding.FreshClaim) (a : Embedding.AuthClaim) :
    ¬ PaidFrom Embedding.Bridge (Sum.inr f) (Sum.inl a) :=
  closed_lane_blocks_paidFrom (freshness_to_authority_closed_lane f a)

/-- If a local kernel admits only authority-lane claims, it cannot derive a freshness claim
    through the existing WDC embedding bridge. -/
theorem no_lift_from_authority_lane_to_freshness {K : Embedding.Claim → Prop}
    (hK : ∀ c, K c → AuthorityLane c) (f : Embedding.FreshClaim) :
    ¬ Lift K Embedding.Bridge (Sum.inr f) :=
  closed_lane_blocks_lift authorityLane_closed hK (by
    rintro ⟨_a, h⟩
    cases h)

/-- If a local kernel admits only freshness-lane claims, it cannot derive an authority claim
    through the existing WDC embedding bridge. -/
theorem no_lift_from_freshness_lane_to_authority {K : Embedding.Claim → Prop}
    (hK : ∀ c, K c → FreshnessLane c) (a : Embedding.AuthClaim) :
    ¬ Lift K Embedding.Bridge (Sum.inl a) :=
  closed_lane_blocks_lift freshnessLane_closed hK (by
    rintro ⟨_f, h⟩
    cases h)

end LeanProofs.Admissibility.WitnessedReachability
