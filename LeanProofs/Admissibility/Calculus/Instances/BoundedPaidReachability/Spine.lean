/-
  Admissibility.Calculus.Instances.BoundedPaidReachability.Spine  --  the
  exact bounded dynamic spine adapter

  EXTRACTED 2026-07-18 from private skunkworks
  (formalization/Calculi/Scratch/CrossCalculus/BoundedPaidSpine.lean, the
  one-owner leaf split out of the combined instance module by the rung-4
  sanitation) as part of rung 4 of the Admissibility Calculus promotion
  campaign. Operator-ratified 2026-07-18; recompiled and
  axiom-re-attested here on arrival. Normalized-source-equal to its
  private source after only the declared import, namespace, and comment
  substitutions.

  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: STABLE-SURFACE
  This module is part of the exact `LeanProofs.Admissibility.Calculus`
  stable root.

  The dynamic instance carries the complete barred-claim/barrier packet:
  the obstruction domain is `RefusalPacket boundedPaidReachability`
  itself, so the decoder is TOTAL — an identity representation, not an
  accident of omitted malformed values. The barrier is transported as
  native data, never recomputed from a claim; two distinct proof-relevant
  refusals at the same claim index encode distinctly (the research tree's
  same-claim barrier audit keeps that boundary executable).

  Bonus impossibility: the witnessed claim admits NO barrier at all
  (`bounded_paid_no_barrier_for_funded`) — refusal evidence for a
  reachable goal is not merely absent but uninhabited.

  Frozen receipts: 4 — `bounded_paid_no_barrier_for_funded` axiom-free;
  the other three exactly `[propext]`.
-/


import LeanProofs.Admissibility.Calculus.Spine
import LeanProofs.Admissibility.Calculus.Instances.BoundedPaidReachability

namespace Admissibility.Calculus.Instances.BoundedPaidReachability

open Admissibility.PathVerdict

/-! ## The dynamic instance on the spine -/

/-- The complete dynamic refusal transported as data.  The packet retains both
    the claimed origin and the exact forward-closed barrier. -/
abbrev BoundedPaidObstruction := RefusalPacket boundedPaidReachability

/-- The reachability encoding carries the complete refusal packet rather than
    recomputing a selected barrier from the claim. -/
def boundedPaidSpine : LosslessEncoding boundedPaidReachability where
  δ := BoundedPaidObstruction
  encode := fun c r => ⟨c, r⟩
  decode := some
  decode_encode := fun _ _ => rfl
  encode_decode := by
    intro d packet decoded
    exact (Option.some.inj decoded).symm

/-- Funnel soundness composed with the no-distortion receipt: the spine
    verdict for a paid claim is authority-bearing exactly when a lawful
    history exists — trace-or-barrier discipline on the spine, no
    endpoint inspection anywhere. -/
theorem bounded_paid_funnel_sound_natively (c : PaidClaim) :
    (boundedPaidSpine.funnel c).AuthorityBearing ↔ LawfulFrom c.origin claimed :=
  (boundedPaidSpine.funnel_authority_iff c).trans (authority_iff_lawful_history c)

/-- The checker computes the canonical bounded barrier. -/
theorem bounded_paid_decide_from_bare_returns_exact_barrier :
    boundedPaidReachability.decide .fromBare = .inr bareBarrier := rfl

/-- The spine transports that exact barrier, rather than a claim from which a
    possibly different refusal would have to be reconstructed. -/
theorem bounded_paid_bare_refusal_round_trip :
    boundedPaidSpine.decode
        (boundedPaidSpine.encode PaidClaim.fromBare bareBarrier) =
      some (RefusalPacket.mk PaidClaim.fromBare bareBarrier) :=
  boundedPaidSpine.decode_encode _ _

/-- **Refusal evidence for the witnessed claim is uninhabited.**  No
    barrier over the funded origin exists at all: any forward-closed
    region containing `funded` contains `claimed`.  Witness and refusal
    are not merely exclusive here — the refusal type is empty. -/
theorem bounded_paid_no_barrier_for_funded (B : Barrier funded) : False :=
  B.excludes (B.stays fundedRun B.contains)

#print axioms bounded_paid_funnel_sound_natively
#print axioms bounded_paid_decide_from_bare_returns_exact_barrier
#print axioms bounded_paid_bare_refusal_round_trip
#print axioms bounded_paid_no_barrier_for_funded

end Admissibility.Calculus.Instances.BoundedPaidReachability
