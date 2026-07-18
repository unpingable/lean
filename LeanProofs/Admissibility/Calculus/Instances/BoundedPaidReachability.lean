/-
  Admissibility.Calculus.Instances.BoundedPaidReachability  --  the
  bounded dynamic instance

  EXTRACTED 2026-07-17 from private skunkworks
  (formalization/Calculi/Scratch/CrossCalculus/ReachabilityInstance.lean)
  as part of rung 3 of the Admissibility Calculus promotion campaign.
  Operator-ratified 2026-07-17; recompiled and axiom-re-attested here on
  arrival. Normalized-source-equal to its private source after only the
  declared import, namespace, and comment substitutions.

  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: STABLE-SURFACE
  This module is part of the exact `LeanProofs.Admissibility.Calculus`
  stable root.

  BOUNDEDNESS FENCE (load-bearing, part of the name): the claim domain has
  exactly two constructors (`fromFunded`, `fromBare`) and one fixed
  endpoint (`claimed`). The positive witness is ADMISSION-ONLY — the
  canonical accepted action list contains one `.admit` and no `.pay` —
  so `claimed.paid = []`, the paid book is empty, and the custody theorem
  is vacuous. Both obligation books are empty (`False`). `decide` is a
  hand-written two-case match, total only because `PaidClaim` has two
  constructors: it is NOT saturation, search, synthesis, or general
  reachability decidability. The native substrate still defines a lawful
  `.pay` edge (the barrier must be closed under every native edge); no
  accepted fixture in this family exercises it.

  What the instance DOES establish: claims carry their ORIGIN, not just
  the endpoint; the witness is a replayable run receipt (data); the
  refusal is a forward-closed barrier — refusal as data, not absence of
  proof; standing is fundability of the goal's occurrences from the
  origin's books; and no endpoint-only check is a faithful authority
  judge for this family (`signature_refuses_endpoint_only_checks`).

  The no-distortion receipt is `authority_iff_lawful_history`: signature
  authority is EXACTLY the native `LawfulFrom` predicate over this fixed
  two-claim family — nothing gained, nothing hidden. Its name must not be
  read as a general decision engine.

  Frozen receipts: 6 — `Barrier.stays` axiom-free; the other five exactly
  `[propext]`.
-/


import LeanProofs.Admissibility.Calculus.Instances.BoundedPaidReachability.Native
import LeanProofs.Admissibility.Calculus.Core

namespace Admissibility.Calculus.Instances.BoundedPaidReachability

open Admissibility.Calculus.Instances.BoundedPaidReachability
open Admissibility.Calculus.Instances.BoundedPaidReachability.Staged

/-! ## The bounded fixtures (one owner: this module) -/

/-- The unfunded origin: all three books empty. -/
def bare : State Nat := ⟨[], [], []⟩

/-- The one warrant of the funded scenario: identity 7, granting token 0. -/
def theWarrant : Warrant Nat := ⟨7, 0⟩

/-- The stamped occurrence a lawful admission of `theWarrant` would stage. -/
def stamped : Resource Nat := ⟨0, .admitted 7⟩

/-- The claimed final state: the stamped occurrence sits in the wallet. -/
def claimed : State Nat := ⟨[stamped], [], []⟩

/-- The funded origin: `theWarrant` genuinely held before any move. -/
def funded : State Nat := ⟨[], [theWarrant], []⟩

/-- The replayable receipt itself: one lawful admission from the funded
    origin mints the stamp.  Exposed as data (not squashed) — the dynamic
    instance uses it as a witness. -/
def fundedRun : Run (Step Nat) funded [.admit theWarrant] claimed :=
  .cons (Step.admit (s := funded) (pre := []) (post := []) rfl) .nil

/-- Lawful history: some replayable run carries the origin to the
    endpoint.  The existential's witness IS the audit artifact. -/
def LawfulFrom (origin endpoint : State Nat) : Prop :=
  ∃ as, Nonempty (Run (Step Nat) origin as endpoint)

/-! ## The two-claim governed family -/

/-- The two fixture claims: reach `claimed` from the funded origin, or
    from the bare one.  The origin is part of the claim — endpoint
    inspection cannot distinguish these two claims. -/
inductive PaidClaim where
  | fromFunded
  | fromBare
deriving DecidableEq, Repr

/-- The claimed origin. -/
def PaidClaim.origin : PaidClaim → State Nat
  | .fromFunded => funded
  | .fromBare => bare

/-- A forward-closed barrier: contains the origin, closed under every
    lawful step, excludes the goal.  The dynamic family's native refusal
    shape, hand-built for this fixed bare-origin claim — not a promoted
    general saturation certificate. -/
structure Barrier (origin : State Nat) where
  region : State Nat → Prop
  contains : region origin
  closed : ∀ {s a s'}, region s → Step Nat s a s' → region s'
  excludes : ¬ region claimed

/-- A lawful run cannot leave a barrier's region. -/
theorem Barrier.stays {origin : State Nat} (B : Barrier origin)
    {s : State Nat} {as : List (Action Nat)} {f : State Nat}
    (run : Run (Step Nat) s as f) (hs : B.region s) : B.region f := by
  induction run with
  | nil => exact hs
  | cons step rest ih => exact ih (B.closed hs step)

/-- The bare origin is stuck: both books that could enable an edge are
    empty, so the singleton region `{bare}` is forward-closed and the
    goal is outside it.  Refusal as data, not as absence of proof. -/
def bareBarrier : Barrier bare where
  region := fun s => s = bare
  contains := rfl
  closed := by
    intro s a s' hs step
    subst hs
    cases step with
    | admit held => simp [bare] at held
    | pay held => simp [bare] at held
  excludes := by decide

/-- BoundedPaidReachability (fixture claims) as a governed family. -/
def boundedPaidReachability : GovernedFamily where
  Claim := PaidClaim
  Witness := fun c =>
    (as : List (Action Nat)) × Run (Step Nat) c.origin as claimed
  Refusal := fun c => Barrier c.origin
  Standing := fun c =>
    ∀ r ∈ claimed.wallet,
      (r ∈ c.origin.wallet ∨ r ∈ c.origin.paid) ∨
        ∃ w, w ∈ c.origin.warrants ∧ r = ⟨w.grants, .admitted w.id⟩
  Custody := fun c =>
    ∀ r ∈ claimed.paid,
      (r ∈ c.origin.wallet ∨ r ∈ c.origin.paid) ∨
        ∃ w, w ∈ c.origin.warrants ∧ r = ⟨w.grants, .admitted w.id⟩
  Obligation := fun _ => False
  exclusive := fun {_c} w B => B.excludes (B.stays w.2 B.contains)
  witness_requires_standing := fun {_c} w r hr =>
    Staged.Run.occurrence_provenance w.2 r (Or.inl hr)
  witness_preserves_custody := fun {_c} w r hr =>
    Staged.Run.occurrence_provenance w.2 r (Or.inr hr)
  decide := fun c =>
    match c with
    | .fromFunded => .inl ⟨[.admit theWarrant], fundedRun⟩
    | .fromBare => .inr bareBarrier

/-- **No-distortion receipt.**  Signature authority is exactly the native
    lawful-history predicate.  The signature adds no reachability and
    hides none. -/
theorem authority_iff_lawful_history (c : PaidClaim) :
    boundedPaidReachability.Authority c ↔ LawfulFrom c.origin claimed :=
  ⟨fun ⟨⟨as, run⟩⟩ => ⟨as, ⟨run⟩⟩, fun ⟨as, ⟨run⟩⟩ => ⟨⟨as, run⟩⟩⟩

/-- The bare claim has no standing: the stamped occurrence is fundable
    from none of the bare origin's books. -/
theorem bare_claim_has_no_standing :
    ¬ boundedPaidReachability.Standing .fromBare := by
  intro h
  rcases h stamped (by simp [claimed]) with (hw | hp) | ⟨w, hw, _⟩
  · simp [PaidClaim.origin, bare] at hw
  · simp [PaidClaim.origin, bare] at hp
  · simp [PaidClaim.origin, bare] at hw

/-- The retro-stamped claim's authority is refuted in the STANDING book — the same generic
    law for every instance — never by inspecting the stamp. -/
theorem retro_claim_refused_for_want_of_standing :
    ¬ boundedPaidReachability.Authority .fromBare :=
  fun h => bare_claim_has_no_standing
    (boundedPaidReachability.authority_requires_standing h)

/-- The bare claim's custody book is intact (vacuously — nothing was paid) while its
    authority is refuted.  Custody grants nothing here either; there is
    no signature operation from the custody book into the witness. -/
theorem custody_does_not_grant_dynamic_authority :
    boundedPaidReachability.Custody .fromBare ∧
      ¬ boundedPaidReachability.Authority .fromBare :=
  ⟨fun r hr => by simp [claimed] at hr,
   boundedPaidReachability.refusal_refutes_authority bareBarrier⟩

/-- Both fixture claims project to the same endpoint, one is witnessed, one is refused, so no
    endpoint-only check is a faithful authority judge for this family.
    Instance of the generic `no_claim_erasing_check_is_faithful`. -/
theorem signature_refuses_endpoint_only_checks :
    ¬ ∃ check : State Nat → Bool,
        ∀ c : PaidClaim, check claimed = true ↔
          boundedPaidReachability.Authority c :=
  boundedPaidReachability.no_claim_erasing_check_is_faithful
    (fun _ => claimed) (c1 := .fromFunded) (c2 := .fromBare) rfl
    ⟨[.admit theWarrant], fundedRun⟩ bareBarrier

#print axioms Barrier.stays
#print axioms authority_iff_lawful_history
#print axioms bare_claim_has_no_standing
#print axioms retro_claim_refused_for_want_of_standing
#print axioms custody_does_not_grant_dynamic_authority
#print axioms signature_refuses_endpoint_only_checks

end Admissibility.Calculus.Instances.BoundedPaidReachability
