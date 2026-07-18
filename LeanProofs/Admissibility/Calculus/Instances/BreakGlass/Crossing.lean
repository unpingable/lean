/-
  Admissibility.Calculus.Instances.BreakGlass — Crossing: the stored-decision Weathering/BreakGlass crossing

  EXTRACTED 2026-07-18 from private skunkworks (Calculi/Scratch/CrossCalculus/BreakGlassOriginBoundCrossing.lean, reconciliation
  commit 85edee78d686) as rung 7 — the terminal rung — of the
  Admissibility Calculus promotion campaign. Operator-ratified 2026-07-18
  with explicit axiom-footprint acceptance; recompiled and
  axiom-re-attested here on arrival. Normalized-source-equal to its
  private source after only the declared import, namespace, and
  custody-header substitutions.

  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: STABLE-SURFACE
  This module is part of the exact `LeanProofs.Admissibility.Calculus`
  stable root. Frozen surface: 15 receipts.

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

import LeanProofs.Admissibility.Calculus.Crossing
import LeanProofs.Admissibility.Calculus.Instances.Weathering.Spine
import LeanProofs.Admissibility.Calculus.Instances.BreakGlass.Spine
import LeanProofs.Admissibility.Calculus.Instances.BreakGlass.Comparison

namespace Admissibility.Calculus.Instances.BreakGlass

open Admissibility.Calculus.Instances.Weathering
open Admissibility.Calculus.Instances.BreakGlass.OriginBound
open Admissibility.Calculus.Instances.BreakGlass.OriginBound.EndToEnd
open Admissibility.Calculus.Instances.Weathering
open Admissibility.Calculus.Crossing
open Admissibility.Calculus.Comparison
open Admissibility.Authority

noncomputable section

/-! ## One stored crossing over the terminal family -/

/-- Weathering is only the left gate; the right family is the complete
    origin-bound BreakGlass governed family and its exact refusal spine. -/
def weatheringBreakGlass (atoms : Atoms) : Crossing.Spec where
  leftFamily := weathering
  rightFamily := governedFamily atoms
  leftSpine := weatherSpine
  rightSpine := originBoundSpine atoms

abbrev BreakGlassCrossClaim (atoms : Atoms) :=
  Crossing.Claim (weatheringBreakGlass atoms)

def crossedClaim (atoms : Atoms) (claim : BreakGlass.Claim) :
    BreakGlassCrossClaim atoms :=
  ⟨(.fresh, .relyDirectly), claim⟩

def nativeCrossedClaim (atoms : Atoms) (phase : Phase) :
    BreakGlassCrossClaim atoms :=
  crossedClaim atoms (nativeClaim atoms phase)

def freshWeatherWitness : weathering.Witness (.fresh, .relyDirectly) :=
  ⟨Admissible.rely rfl⟩

/-- The sole specialized evaluation boundary.  The generic `evaluate` calls
    the two native decisions once and stores them in this packet. -/
def crossCheck (atoms : Atoms) (claim : BreakGlass.Claim) :
    Crossing.CheckedPacket (weatheringBreakGlass atoms) :=
  Crossing.evaluate (weatheringBreakGlass atoms)
    (crossedClaim atoms claim)

def ordinaryCrossRefusal (atoms : Atoms) :
    Refusal atoms (nativeClaim atoms .ordinaryLaunder) :=
  .ordinaryLaunder rfl rfl (ordinaryLaunderRefusal atoms)

def auditCrossRefusal (atoms : Atoms) :
    Refusal atoms (nativeClaim atoms .auditLaunder) :=
  .auditLaunder rfl rfl (auditLaunderRefusal atoms)

def foreignCrossRefusal (atoms : Atoms)
    (claim : BreakGlass.Claim)
    (foreign : claim.origin ≠ atoms.origin) : Refusal atoms claim :=
  .foreignOrigin ⟨foreign⟩

/-! ## Native controls and exact stored refusal branches -/

/-- All four native lifecycle phases remain admitted after crossing. -/
theorem native_lifecycle_crosses_clean (atoms : Atoms) :
    (crossCheck atoms (nativeClaim atoms .prospective)).checked.result.isLeft =
        true ∧
      (crossCheck atoms (nativeClaim atoms .attempted)).checked.result.isLeft =
        true ∧
      (crossCheck atoms (nativeClaim atoms .committed)).checked.result.isLeft =
        true ∧
      (crossCheck atoms (nativeClaim atoms .settled)).checked.result.isLeft =
        true := by
  constructor
  · apply (crossCheck atoms
      (nativeClaim atoms .prospective)).checked.result_isLeft_iff_authority.mpr
    exact ⟨⟨freshWeatherWitness, ⟨rfl, permit atoms, rfl⟩⟩⟩
  constructor
  · apply (crossCheck atoms
      (nativeClaim atoms .attempted)).checked.result_isLeft_iff_authority.mpr
    exact ⟨⟨freshWeatherWitness, ⟨rfl, attempt atoms, rfl⟩⟩⟩
  constructor
  · apply (crossCheck atoms
      (nativeClaim atoms .committed)).checked.result_isLeft_iff_authority.mpr
    exact ⟨⟨freshWeatherWitness, ⟨rfl, commit atoms, rfl⟩⟩⟩
  · apply (crossCheck atoms
      (nativeClaim atoms .settled)).checked.result_isLeft_iff_authority.mpr
    exact ⟨⟨freshWeatherWitness,
      ⟨rfl, commit atoms, rfl, settlement atoms⟩⟩⟩

/-- Ordinary-authority laundering is a right-family refusal; the successful
    Weathering witness is retained in the stored result. -/
theorem ordinary_launder_crossing_refuses_exactly (atoms : Atoms) :
    (crossCheck atoms
      (nativeClaim atoms .ordinaryLaunder)).checked.result =
        .inr (.rightRefused freshWeatherWitness
          (ordinaryCrossRefusal atoms)) := by
  simp [crossCheck, Crossing.evaluate, Crossing.check,
    crossedClaim, weatheringBreakGlass, weathering, governedFamily,
    nativeClaim, Weather.canTestify, ordinaryCrossRefusal,
    freshWeatherWitness] <;>
    congr <;> apply Subsingleton.elim

/-- Audit-clean laundering is a distinct right-family refusal. -/
theorem audit_launder_crossing_refuses_exactly (atoms : Atoms) :
    (crossCheck atoms
      (nativeClaim atoms .auditLaunder)).checked.result =
        .inr (.rightRefused freshWeatherWitness
          (auditCrossRefusal atoms)) := by
  simp [crossCheck, Crossing.evaluate, Crossing.check,
    crossedClaim, weatheringBreakGlass, weathering, governedFamily,
    nativeClaim, Weather.canTestify, auditCrossRefusal,
    freshWeatherWitness] <;>
    congr <;> apply Subsingleton.elim

/-- A foreign-origin claim remains a structured BreakGlass refusal after the
    fresh gate; origin mismatch is not flattened into a crossing bit. -/
theorem foreign_crossing_refuses_exactly
    (atoms : Atoms) (claim : BreakGlass.Claim)
    (foreign : claim.origin ≠ atoms.origin) :
    (crossCheck atoms claim).checked.result =
      .inr (.rightRefused freshWeatherWitness
        (foreignCrossRefusal atoms claim foreign)) := by
  simp [crossCheck, Crossing.evaluate, Crossing.check,
    crossedClaim, weatheringBreakGlass, weathering, Weather.canTestify,
    foreign_claim_computes_structured_refusal atoms claim foreign] <;>
    congr <;> apply Subsingleton.elim

/-- Foreign origin, phase, and the complete native refusal all survive the
    located crossing and exact decoder. -/
theorem foreign_crossing_location_decodes_exactly
    (atoms : Atoms) (claim : BreakGlass.Claim)
    (foreign : claim.origin ≠ atoms.origin) :
    (crossCheck atoms claim).checked.located =
        ⟨[(.right, .domain (.inr
          ((originBoundSpine atoms).encode claim
            (foreignCrossRefusal atoms claim foreign))))]⟩ ∧
      (originBoundSpine atoms).decode
          ((originBoundSpine atoms).encode claim
            (foreignCrossRefusal atoms claim foreign)) =
        some ⟨claim, foreignCrossRefusal atoms claim foreign⟩ :=
  (crossCheck atoms claim).checked.right_refusal_located_and_decode
    freshWeatherWitness (foreignCrossRefusal atoms claim foreign)
    (foreign_crossing_refuses_exactly atoms claim foreign)

/-- Ordinary-authority laundering retains its exact native claim and refusal
    after crossing; the fresh left witness cannot flatten the denial into an
    anonymous failed bit. -/
theorem ordinary_launder_crossing_location_decodes_exactly (atoms : Atoms) :
    (crossCheck atoms
      (nativeClaim atoms .ordinaryLaunder)).checked.located =
        ⟨[(.right, .domain (.inr
          ((originBoundSpine atoms).encode
            (nativeClaim atoms .ordinaryLaunder)
            (ordinaryCrossRefusal atoms))))]⟩ ∧
      (originBoundSpine atoms).decode
          ((originBoundSpine atoms).encode
            (nativeClaim atoms .ordinaryLaunder)
            (ordinaryCrossRefusal atoms)) =
        some ⟨nativeClaim atoms .ordinaryLaunder,
          ordinaryCrossRefusal atoms⟩ :=
  (crossCheck atoms
    (nativeClaim atoms .ordinaryLaunder)).checked
      |>.right_refusal_located_and_decode freshWeatherWitness
        (ordinaryCrossRefusal atoms)
        (ordinary_launder_crossing_refuses_exactly atoms)

/-- Audit laundering remains independently located and exactly decodable;
    it cannot alias the ordinary-authority refusal at the crossing. -/
theorem audit_launder_crossing_location_decodes_exactly (atoms : Atoms) :
    (crossCheck atoms
      (nativeClaim atoms .auditLaunder)).checked.located =
        ⟨[(.right, .domain (.inr
          ((originBoundSpine atoms).encode
            (nativeClaim atoms .auditLaunder)
            (auditCrossRefusal atoms))))]⟩ ∧
      (originBoundSpine atoms).decode
          ((originBoundSpine atoms).encode
            (nativeClaim atoms .auditLaunder)
            (auditCrossRefusal atoms)) =
        some ⟨nativeClaim atoms .auditLaunder,
          auditCrossRefusal atoms⟩ :=
  (crossCheck atoms
    (nativeClaim atoms .auditLaunder)).checked
      |>.right_refusal_located_and_decode freshWeatherWitness
        (auditCrossRefusal atoms)
        (audit_launder_crossing_refuses_exactly atoms)

/-- The crossing's two laundering diagnostics remain different in the exact
    right-family domain because their claim phases remain different. -/
theorem crossing_laundering_encodings_remain_distinct (atoms : Atoms) :
    (originBoundSpine atoms).encode
        (nativeClaim atoms .ordinaryLaunder)
        (ordinaryCrossRefusal atoms) ≠
      (originBoundSpine atoms).encode
        (nativeClaim atoms .auditLaunder)
        (auditCrossRefusal atoms) := by
  intro encodingsEqual
  have claimsEqual := congrArg RefusalPacket.claim encodingsEqual
  have phasesEqual := congrArg Claim.phase claimsEqual
  exact Phase.noConfusion phasesEqual

/-! ## Comparison, origin, obligation, and native-history preservation -/

/-- Rung 7 consumes the admitted exact checked-packet comparison rather than
    constructing a second checker-shaped relation. -/
def breakGlassCrossCheckExact (atoms : Atoms) :=
  checkedProjectionExact (weatheringBreakGlass atoms)

theorem cross_check_acceptance_iff_authority
    (atoms : Atoms) (claim : BreakGlass.Claim) :
    (crossCheck atoms claim).checked.result.isLeft = true ↔
      Crossing.Authority (weatheringBreakGlass atoms)
        (crossedClaim atoms claim) :=
  by
    simpa [checkedProjection, authorityView, checkedView] using
      ((breakGlassCrossCheckExact atoms).holds_iff
        (crossCheck atoms claim)).symm

/-- An accepted crossing exposes native BreakGlass authority and therefore
    equality with the exact lifecycle origin. -/
theorem crossing_authority_retains_break_glass_origin
    (atoms : Atoms) {claim : BreakGlass.Claim}
    (authority :
      Crossing.Authority (weatheringBreakGlass atoms)
        (crossedClaim atoms claim)) :
    claim.origin = atoms.origin := by
  have components :=
    (authority_iff_components (weatheringBreakGlass atoms)
      (crossedClaim atoms claim)).mp authority
  exact authority_retains_claim_origin atoms components.2

/-- The crossing consumes C1 without upgrading the permit's retained ordinary
    verdict.  Accepted composite authority retains both native BreakGlass
    authority and the native denial; it does not fabricate an ordinary
    `AuthorizedStep`. -/
theorem crossing_does_not_absorb_exceptional_into_authorized_verdict
    (atoms : Atoms) {claim : BreakGlass.Claim}
    (authority :
      Crossing.Authority (weatheringBreakGlass atoms)
        (crossedClaim atoms claim)) :
    (governedFamily atoms).Authority claim ∧
      (permit atoms).ordinaryVerdict = .denied := by
  have components :=
    (authority_iff_components (weatheringBreakGlass atoms)
      (crossedClaim atoms claim)).mp authority
  exact ⟨components.2, (ordinaryLaunderRefusal atoms).denied⟩

/-- Commit and settlement both cross cleanly while the exact native
    obligation opens and then closes.  The generic crossing observes this
    lifecycle; it does not define or mutate the obligation book. -/
theorem crossing_exposes_native_obligation_lifecycle (atoms : Atoms) :
    (crossCheck atoms (nativeClaim atoms .committed)).checked.result.isLeft =
        true ∧
      (governedFamily atoms).Obligation
        (nativeClaim atoms .committed) ∧
      (crossCheck atoms (nativeClaim atoms .settled)).checked.result.isLeft =
        true ∧
      ¬ (governedFamily atoms).Obligation
        (nativeClaim atoms .settled) :=
  ⟨(native_lifecycle_crosses_clean atoms).2.2.1,
    commit_opens_exact_obligation atoms,
    (native_lifecycle_crosses_clean atoms).2.2.2,
    settlement_closes_exact_obligation atoms⟩

/-- A successful settled crossing carries the native origin/history-bound
    reconciliation witness all the way through its right component. -/
theorem settled_crossing_witness_carries_exact_reconciliation
    (atoms : Atoms)
    (witness : Crossing.Witness (weatheringBreakGlass atoms)
      (nativeCrossedClaim atoms .settled)) :
    Reconciles witness.right.nativeCommit.after
      (.defaulted (defaultRecord atoms)) (finalLedger atoms) :=
  witness.right.nativeSettlement

/-- The settled crossing visibly retains the exact attested opening consumed
    by reconciliation: native book membership, event binding, and the full
    `ValidAgainst` history check survive the final adapter. -/
theorem settled_crossing_exposes_attested_opening
    (atoms : Atoms)
    (witness : Crossing.Witness (weatheringBreakGlass atoms)
      (nativeCrossedClaim atoms .settled)) :
    ∃ obligation entry,
      obligation ∈ witness.right.nativeCommit.after.obligations ∧
      (ReconciliationDisposition.defaulted
        (defaultRecord atoms)).Matches obligation ∧
      entry ∈ witness.right.nativeCommit.after.auditTrail.entries ∧
      entry.obligation = obligation ∧
      entry.commitment.event = obligation.openedBy ∧
      entry.ValidAgainst
        witness.right.nativeCommit.after.evidence
        witness.right.nativeCommit.after.usedPermits
        witness.right.nativeCommit.after.executionReceipts
        witness.right.nativeCommit.after.obligations :=
  reconciliation_exposes_valid_opening
    (settled_crossing_witness_carries_exact_reconciliation atoms witness)

/-- Settlement standing remains present at the audit-laundering claim, but
    the stored crossing refuses and the exact native history remains unclean.
    No branch is discharged by a vacuous standing antecedent. -/
theorem audit_launder_crossing_retains_standing_but_rejects
    (atoms : Atoms) :
    (governedFamily atoms).Standing
        (nativeClaim atoms .auditLaunder) ∧
      (crossCheck atoms
        (nativeClaim atoms .auditLaunder)).checked.result =
          .inr (.rightRefused freshWeatherWitness
            (auditCrossRefusal atoms)) ∧
      ¬ (finalLedger atoms).auditTrail.Clean :=
  ⟨audit_launder_has_settlement_standing atoms,
    audit_launder_crossing_refuses_exactly atoms,
    native_settled_history_is_not_audit_clean atoms⟩

#print axioms native_lifecycle_crosses_clean
#print axioms ordinary_launder_crossing_refuses_exactly
#print axioms audit_launder_crossing_refuses_exactly
#print axioms foreign_crossing_refuses_exactly
#print axioms foreign_crossing_location_decodes_exactly
#print axioms ordinary_launder_crossing_location_decodes_exactly
#print axioms audit_launder_crossing_location_decodes_exactly
#print axioms crossing_laundering_encodings_remain_distinct
#print axioms cross_check_acceptance_iff_authority
#print axioms crossing_authority_retains_break_glass_origin
#print axioms crossing_does_not_absorb_exceptional_into_authorized_verdict
#print axioms crossing_exposes_native_obligation_lifecycle
#print axioms settled_crossing_witness_carries_exact_reconciliation
#print axioms settled_crossing_exposes_attested_opening
#print axioms audit_launder_crossing_retains_standing_but_rejects

end

end Admissibility.Calculus.Instances.BreakGlass
