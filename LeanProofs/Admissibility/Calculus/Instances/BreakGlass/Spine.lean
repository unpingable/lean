/-
  Admissibility.Calculus.Instances.BreakGlass — Spine: the exact dependent refusal-packet encoding

  EXTRACTED 2026-07-18 from private skunkworks (Calculi/Scratch/CrossCalculus/BreakGlassOriginBoundSpine.lean, reconciliation
  commit 85edee78d686) as rung 7 — the terminal rung — of the
  Admissibility Calculus promotion campaign. Operator-ratified 2026-07-18
  with explicit axiom-footprint acceptance; recompiled and
  axiom-re-attested here on arrival. Normalized-source-equal to its
  private source after only the declared import, namespace, and
  custody-header substitutions.

  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: STABLE-SURFACE
  This module is part of the exact `LeanProofs.Admissibility.Calculus`
  stable root. Frozen surface: 9 receipts.

  BINDING FENCES (rung-7 packet, operator-ratified): the family is closed
  only relative to a consumer-supplied `Atoms` (origin, state, actor,
  step); no closed inhabitant of `Atoms` or the abstract public substrate
  is claimed. State change on commit is proved only under the explicit
  `state != applyStep state step` hypothesis. The C1 result is retained
  ordinary-VERDICT separation — it neither constructs nor rejects a
  native `AuthorizedStep`. Settlement standing does not imply audit
  cleanliness. The bounded audit trail is a singleton, so reordering is
  vacuous, not a multi-entry theorem. No runtime attestor honesty, origin
  allocation uniqueness, discharge/payment lifecycle, or general
  transition universe is claimed. The stable footprint includes
  `Quot.sound` and `Classical.choice` over the declared opaque public
  substrate — named per-theorem in the research-tree manifest and
  accepted explicitly at ratification. The closed seven-entry rung-5
  `EntryIndex` is unchanged; the legacy fixed-`Atoms` exploit remains
  byte-pinned adverse custody in the research tree.
-/


import LeanProofs.Admissibility.Calculus.Spine
import LeanProofs.Admissibility.Calculus.Instances.BreakGlass

namespace Admissibility.Calculus.Instances.BreakGlass

open Admissibility.PathVerdict
open Admissibility.Calculus.Instances.BreakGlass.OriginBound
open Admissibility.Calculus.Instances.BreakGlass.OriginBound.EndToEnd

noncomputable section

/-- The exact negative decision for one bounded BreakGlass target family. -/
abbrev BreakGlassObstruction (atoms : Atoms) :=
  RefusalPacket (governedFamily atoms)

/-- Identity transport of the complete native refusal packet. -/
def originBoundSpine (atoms : Atoms) :
    LosslessEncoding (governedFamily atoms) where
  δ := BreakGlassObstruction atoms
  encode := fun claim refusal => ⟨claim, refusal⟩
  decode := some
  decode_encode := fun _ _ => rfl
  encode_decode := by
    intro d packet decoded
    exact (Option.some.inj decoded).symm

def ordinaryLaunderRefusalPacket (atoms : Atoms) :
    BreakGlassObstruction atoms :=
  ⟨nativeClaim atoms .ordinaryLaunder,
    .ordinaryLaunder rfl rfl (ordinaryLaunderRefusal atoms)⟩

def auditLaunderRefusalPacket (atoms : Atoms) :
    BreakGlassObstruction atoms :=
  ⟨nativeClaim atoms .auditLaunder,
    .auditLaunder rfl rfl (auditLaunderRefusal atoms)⟩

def foreignRefusalPacket (atoms : Atoms) (claim : Claim)
    (foreign : claim.origin ≠ atoms.origin) : BreakGlassObstruction atoms :=
  ⟨claim, .foreignOrigin ⟨foreign⟩⟩

/-- The family-specific statement of the generic exact round trip. -/
theorem exact_refusal_round_trip
    (atoms : Atoms) (claim : Claim) (refusal : Refusal atoms claim) :
    (originBoundSpine atoms).decode
        ((originBoundSpine atoms).encode claim refusal) =
      some (RefusalPacket.mk claim refusal) :=
  (originBoundSpine atoms).decode_encode claim refusal

/-- The exact spine retains the family's two-sided authority judgment. -/
theorem origin_bound_funnel_authority_iff
    (atoms : Atoms) (claim : Claim) :
    ((originBoundSpine atoms).funnel claim).AuthorityBearing ↔
      (governedFamily atoms).Authority claim :=
  (originBoundSpine atoms).funnel_authority_iff claim

/-- Every claim computes either a clean witness branch or an exact singleton
    refusal whose complete packet survives decoding. -/
theorem origin_bound_spine_decision_complete
    (atoms : Atoms) (claim : Claim) :
    (∃ witness,
      (governedFamily atoms).decide claim = .inl witness ∧
        (originBoundSpine atoms).funnel claim = PathVerdict.clean) ∨
    (∃ refusal,
      (governedFamily atoms).decide claim = .inr refusal ∧
        (originBoundSpine atoms).funnel claim =
          ⟨[.domain (RefusalPacket.mk claim refusal)]⟩ ∧
        (originBoundSpine atoms).decode
            (RefusalPacket.mk claim refusal) =
          some (RefusalPacket.mk claim refusal)) := by
  cases decided : (governedFamily atoms).decide claim with
  | inl witness =>
      refine Or.inl ⟨witness, rfl, ?_⟩
      simp [SpineEncoding.funnel, decided]
  | inr refusal =>
      refine Or.inr ⟨refusal, rfl, ?_, rfl⟩
      simp [SpineEncoding.funnel, decided, originBoundSpine]

/-- All four admitted native lifecycle phases compute clean. -/
theorem native_lifecycle_phases_funnel_clean (atoms : Atoms) :
    (originBoundSpine atoms).funnel
        (nativeClaim atoms .prospective) = PathVerdict.clean ∧
      (originBoundSpine atoms).funnel
        (nativeClaim atoms .attempted) = PathVerdict.clean ∧
      (originBoundSpine atoms).funnel
        (nativeClaim atoms .committed) = PathVerdict.clean ∧
      (originBoundSpine atoms).funnel
        (nativeClaim atoms .settled) = PathVerdict.clean := by
  simp [SpineEncoding.funnel, governedFamily, nativeClaim]

/-- Ordinary laundering computes and decodes its exact native refusal. -/
theorem ordinary_launder_funnels_exact_refusal (atoms : Atoms) :
    (originBoundSpine atoms).funnel
        (nativeClaim atoms .ordinaryLaunder) =
        ⟨[.domain (ordinaryLaunderRefusalPacket atoms)]⟩ ∧
      (originBoundSpine atoms).decode
          (ordinaryLaunderRefusalPacket atoms) =
        some (ordinaryLaunderRefusalPacket atoms) := by
  simp [SpineEncoding.funnel, governedFamily, nativeClaim,
    originBoundSpine, ordinaryLaunderRefusalPacket]

/-- Audit laundering computes and decodes its independent exact refusal. -/
theorem audit_launder_funnels_exact_refusal (atoms : Atoms) :
    (originBoundSpine atoms).funnel
        (nativeClaim atoms .auditLaunder) =
        ⟨[.domain (auditLaunderRefusalPacket atoms)]⟩ ∧
      (originBoundSpine atoms).decode
          (auditLaunderRefusalPacket atoms) =
        some (auditLaunderRefusalPacket atoms) := by
  simp [SpineEncoding.funnel, governedFamily, nativeClaim,
    originBoundSpine, auditLaunderRefusalPacket]

/-- An arbitrary foreign-origin claim computes and decodes that exact claim's
    structured foreign refusal. -/
theorem foreign_claim_funnels_exact_refusal
    (atoms : Atoms) (claim : Claim)
    (foreign : claim.origin ≠ atoms.origin) :
    (originBoundSpine atoms).funnel claim =
        ⟨[.domain (foreignRefusalPacket atoms claim foreign)]⟩ ∧
      (originBoundSpine atoms).decode
          (foreignRefusalPacket atoms claim foreign) =
        some (foreignRefusalPacket atoms claim foreign) := by
  have decided := foreign_claim_computes_structured_refusal atoms claim foreign
  constructor
  · simpa [originBoundSpine, foreignRefusalPacket] using
      (originBoundSpine atoms).funnel_of_decide_inr decided
  · rfl

/-- The two native laundering coordinates cannot collapse in the exact domain. -/
theorem laundering_refusal_packets_distinct (atoms : Atoms) :
    ordinaryLaunderRefusalPacket atoms ≠
      auditLaunderRefusalPacket atoms := by
  intro packetsEqual
  have claimsEqual := congrArg RefusalPacket.claim packetsEqual
  have phasesEqual := congrArg Claim.phase claimsEqual
  exact Phase.noConfusion phasesEqual

/-- A clean settled funnel still exposes the native origin-qualified
    reconciliation through the family witness; the clean verdict is not an
    alternate settlement proof. -/
theorem settled_funnel_exposes_native_reconciliation
    (atoms : Atoms)
    (clean : ((originBoundSpine atoms).funnel
      (nativeClaim atoms .settled)).AuthorityBearing) :
    ∃ witness : Witness atoms (nativeClaim atoms .settled),
      Reconciles witness.nativeCommit.after
        (.defaulted (defaultRecord atoms)) (finalLedger atoms) := by
  have authority :=
    (origin_bound_funnel_authority_iff atoms
      (nativeClaim atoms .settled)).mp clean
  rcases authority with ⟨witness⟩
  exact ⟨witness,
    settlement_witness_carries_native_reconciliation atoms witness⟩

#print axioms exact_refusal_round_trip
#print axioms origin_bound_funnel_authority_iff
#print axioms origin_bound_spine_decision_complete
#print axioms native_lifecycle_phases_funnel_clean
#print axioms ordinary_launder_funnels_exact_refusal
#print axioms audit_launder_funnels_exact_refusal
#print axioms foreign_claim_funnels_exact_refusal
#print axioms laundering_refusal_packets_distinct
#print axioms settled_funnel_exposes_native_reconciliation

end

end Admissibility.Calculus.Instances.BreakGlass
