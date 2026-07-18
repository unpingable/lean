/-
  Admissibility.Calculus.Instances.WeatheringBoundedPaidCrossing  --  the
  witnessed inhabitant of the crossing law

  EXTRACTED 2026-07-18 from private skunkworks
  (formalization/Calculi/Scratch/CrossCalculus/Rung6Crossing/
  WeatheringBoundedPaid.lean, reconciliation commit e03c1b7abcea, blob
  9ac4cddefc20) as rung 6 of the Admissibility Calculus promotion
  campaign. Operator-ratified 2026-07-18; recompiled and axiom-re-attested
  here on arrival. Normalized-source-equal to its private source after
  only the declared import, namespace, and comment substitutions.
  Declares namespace `Admissibility.Calculus.Crossing` (shared with the
  generic core, as in the private source).

  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: STABLE-SURFACE
  This module is part of the exact `LeanProofs.Admissibility.Calculus`
  stable root.

  CLAIM FENCE (binding on any public claim): the concrete instance
  establishes crossing behavior for the declared Weathering and
  bounded-paid judgment shapes. It does NOT establish payment,
  settlement, obligation transition, or non-vacuous custody — the
  vacuous-custody and empty-obligation disclosures below are part of the
  ratified surface and travel with the positive laws. "Weathering and
  paid discharge compose exactly" is NOT proved here; the paidDischarge
  separation remains research-tree evidence.

  One Weathering gate crossed with one bounded paid-reachability
  passage. The four fixtures exercise every branch of the generic
  stored-decision checker: a green gate cannot cure an unfunded passage,
  a funded passage cannot cure a stale gate, and the double fault names
  and exactly decodes both native refusals with neither shadowing the
  other.

  Frozen surface: 14 receipts, all exactly `[propext]`.
-/


import LeanProofs.Admissibility.Calculus.Crossing
import LeanProofs.Admissibility.Calculus.Instances.Weathering.Spine
import LeanProofs.Admissibility.Calculus.Instances.BoundedPaidReachability.Spine

namespace Admissibility.Calculus.Crossing

open Admissibility.Calculus.Instances.Weathering
open Admissibility.Calculus.Instances.BoundedPaidReachability
open Admissibility.Calculus.Instances.BoundedPaidReachability
open Admissibility.Calculus.Instances.BoundedPaidReachability.Staged

/-! ## The concrete specification and four branch controls -/

/-- Weathering is the left gate; bounded paid reachability is the right
    passage.  Both use the exact rung-4 refusal-packet spines. -/
def weatheringBoundedPaid : Spec where
  leftFamily := weathering
  rightFamily := boundedPaidReachability
  leftSpine := weatherSpine
  rightSpine := boundedPaidSpine

abbrev WeatheringPaidClaim := Claim weatheringBoundedPaid
abbrev WeatheringPaidWitness (c : WeatheringPaidClaim) :=
  Witness weatheringBoundedPaid c
abbrev WeatheringPaidRefusal (c : WeatheringPaidClaim) :=
  Refusal weatheringBoundedPaid c

/-- Nearby controls differing only in the intended discriminants. -/
def freshFunded : WeatheringPaidClaim :=
  ⟨(.fresh, .relyDirectly), .fromFunded⟩

def staleFunded : WeatheringPaidClaim :=
  ⟨(.stale, .relyDirectly), .fromFunded⟩

def freshBare : WeatheringPaidClaim :=
  ⟨(.fresh, .relyDirectly), .fromBare⟩

def staleBare : WeatheringPaidClaim :=
  ⟨(.stale, .relyDirectly), .fromBare⟩

def freshGateWitness : weathering.Witness (.fresh, .relyDirectly) :=
  ⟨fresh_may_rely⟩

def staleGateRefusal : weathering.Refusal (.stale, .relyDirectly) :=
  ⟨⟨rfl, rfl⟩⟩

def fundedPassageWitness :
    boundedPaidReachability.Witness .fromFunded :=
  ⟨[.admit theWarrant], fundedRun⟩

/-- Clean control: both native witnesses survive in the result. -/
theorem check_fresh_funded_exact :
    (check weatheringBoundedPaid freshFunded).result =
      .inl ⟨freshGateWitness, fundedPassageWitness⟩ :=
  rfl

/-- Static-only control: the passage witness survives beside the gate
    refusal. -/
theorem check_stale_funded_exact :
    (check weatheringBoundedPaid staleFunded).result =
      .inr (.leftRefused staleGateRefusal fundedPassageWitness) :=
  rfl

/-- Dynamic-only control: the gate witness survives beside the passage
    refusal. -/
theorem check_fresh_bare_exact :
    (check weatheringBoundedPaid freshBare).result =
      .inr (.rightRefused freshGateWitness bareBarrier) :=
  rfl

/-- Double-fault control: both native refusals survive in crossing order. -/
theorem check_stale_bare_exact :
    (check weatheringBoundedPaid staleBare).result =
      .inr (.bothRefused staleGateRefusal bareBarrier) :=
  rfl

/-! ## Concrete authority and book boundaries -/

/-- The concrete crossing mints no authority of its own. -/
theorem weathering_paid_authority_iff_components (c : WeatheringPaidClaim) :
    Authority weatheringBoundedPaid c ↔
      weathering.Authority c.left ∧
        boundedPaidReachability.Authority c.right :=
  authority_iff_components weatheringBoundedPaid c

/-- A green Weathering gate cannot cure the native refusal of the unfunded
    passage.  This is the honest bounded replacement for the legacy theorem
    that conjoined an unrelated settled-payment fixture. -/
theorem green_gate_cannot_cure_unfunded_passage :
    weathering.Authority freshBare.left ∧
      ¬ Authority weatheringBoundedPaid freshBare := by
  constructor
  · exact ⟨freshGateWitness⟩
  · intro crossing
    exact retro_claim_refused_for_want_of_standing
      ((weathering_paid_authority_iff_components freshBare).mp crossing).2

/-- Symmetrically, a funded passage cannot cure the stale gate. -/
theorem funded_passage_cannot_cure_stale_gate :
    boundedPaidReachability.Authority staleFunded.right ∧
      ¬ Authority weatheringBoundedPaid staleFunded := by
  constructor
  · exact ⟨fundedPassageWitness⟩
  · intro crossing
    exact weathering_refuses_stale_direct
      ((weathering_paid_authority_iff_components staleFunded).mp crossing).1

/-- Any accepted concrete crossing requires both native standings. -/
theorem weathering_paid_requires_both_standings {c : WeatheringPaidClaim}
    (authority : Authority weatheringBoundedPaid c) :
    weathering.Standing c.left ∧
      boundedPaidReachability.Standing c.right :=
  authority_requires_both_standings authority

/-- Any accepted concrete crossing preserves both native custody judgments. -/
theorem weathering_paid_preserves_both_custodies {c : WeatheringPaidClaim}
    (authority : Authority weatheringBoundedPaid c) :
    weathering.Custody c.left ∧
      boundedPaidReachability.Custody c.right :=
  authority_preserves_both_custodies authority

/-- Scope receipt: the bounded paid custody judgment is vacuous because the
    fixed goal's paid book is empty.  No substantive custody claim is inferred
    from the preceding generic preservation theorem. -/
theorem bounded_paid_component_custody_is_vacuous (c : PaidClaim) :
    boundedPaidReachability.Custody c := by
  intro resource membership
  simp [claimed] at membership

/-- Honest obligation statement for this bounded pair: both component books
    are empty.  There is no transition relation here and therefore no
    "changes only natively" theorem. -/
theorem weathering_paid_component_obligation_books_are_empty
    (c : WeatheringPaidClaim) :
    ¬ weathering.Obligation c.left ∧
      ¬ boundedPaidReachability.Obligation c.right :=
  ⟨fun obligation => obligation, fun obligation => obligation⟩

/-! ## Diagnostic controls -/

/-- The static-only diagnostic names only the gate. -/
theorem stale_funded_location_exact :
    (check weatheringBoundedPaid staleFunded).located =
      ⟨[(.left, .domain (.inl
        (weatherSpine.encode staleFunded.left staleGateRefusal)))]⟩ := by
  unfold CheckedCrossing.located
  rw [show (check weatheringBoundedPaid staleFunded).result =
      .inr (.leftRefused staleGateRefusal fundedPassageWitness) from
    check_stale_funded_exact]
  rfl

/-- The dynamic-only diagnostic names only the passage. -/
theorem fresh_bare_location_exact :
    (check weatheringBoundedPaid freshBare).located =
      ⟨[(.right, .domain (.inr
        (boundedPaidSpine.encode freshBare.right bareBarrier)))]⟩ := by
  unfold CheckedCrossing.located
  rw [show (check weatheringBoundedPaid freshBare).result =
      .inr (.rightRefused freshGateWitness bareBarrier) from
    check_fresh_bare_exact]
  rfl

/-- The double-fault diagnostic names and exactly decodes both native
    refusals; neither segment shadows the other. -/
theorem stale_bare_double_fault_nonshadowing :
    (check weatheringBoundedPaid staleBare).located =
        ⟨[(.left, .domain (.inl
            (weatherSpine.encode staleBare.left staleGateRefusal))),
          (.right, .domain (.inr
            (boundedPaidSpine.encode staleBare.right bareBarrier)))]⟩ ∧
      weatherSpine.decode
          (weatherSpine.encode staleBare.left staleGateRefusal) =
        some ⟨staleBare.left, staleGateRefusal⟩ ∧
      boundedPaidSpine.decode
          (boundedPaidSpine.encode staleBare.right bareBarrier) =
        some ⟨staleBare.right, bareBarrier⟩ :=
  (check weatheringBoundedPaid staleBare).both_refusals_located_and_decode
    staleGateRefusal bareBarrier check_stale_bare_exact

/-- The concrete checker supplies the rung-5 exact-judgment receipt without
    importing the private seven-entry ledger. -/
def weatheringPaidCheckExact := checkedProjectionExact weatheringBoundedPaid

#print axioms check_fresh_funded_exact
#print axioms check_stale_funded_exact
#print axioms check_fresh_bare_exact
#print axioms check_stale_bare_exact
#print axioms weathering_paid_authority_iff_components
#print axioms green_gate_cannot_cure_unfunded_passage
#print axioms funded_passage_cannot_cure_stale_gate
#print axioms weathering_paid_requires_both_standings
#print axioms weathering_paid_preserves_both_custodies
#print axioms bounded_paid_component_custody_is_vacuous
#print axioms weathering_paid_component_obligation_books_are_empty
#print axioms stale_funded_location_exact
#print axioms fresh_bare_location_exact
#print axioms stale_bare_double_fault_nonshadowing

end Admissibility.Calculus.Crossing
