/-
  Admissibility.Calculus.Instances.BreakGlass — Comparison: the terminal C1 and audit separation receipts

  EXTRACTED 2026-07-18 from private skunkworks (Calculi/Scratch/CrossCalculus/BreakGlassOriginBoundComparison.lean, reconciliation
  commit 85edee78d686) as rung 7 — the terminal rung — of the
  Admissibility Calculus promotion campaign. Operator-ratified 2026-07-18
  with explicit axiom-footprint acceptance; recompiled and
  axiom-re-attested here on arrival. Normalized-source-equal to its
  private source after only the declared import, namespace, and
  custody-header substitutions.

  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: STABLE-SURFACE
  This module is part of the exact `LeanProofs.Admissibility.Calculus`
  stable root. Frozen surface: 4 receipts.

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


import LeanProofs.Admissibility.Calculus.Comparison
import LeanProofs.Admissibility.Calculus.Instances.BreakGlass

namespace Admissibility.Calculus.Instances.BreakGlass

open Admissibility.Calculus.Instances.BreakGlass.OriginBound
open Admissibility.Calculus.Instances.BreakGlass.OriginBound.EndToEnd
open Admissibility.Calculus.Comparison
open Admissibility.Authority

noncomputable section

/-! ## Exceptional authority remains separated from the ordinary verdict -/

def exceptionalAuthorityView (atoms : Atoms) : JudgmentView where
  Carrier := Claim
  holds := fun claim => (governedFamily atoms).Authority claim

def ordinaryVerdictView : JudgmentView where
  Carrier := AuthorityVerdict
  holds := fun verdict => verdict = .authorized

/-- The native permit's retained ordinary verdict is the one declared map.
    No adapter turns exceptional admission into ordinary authority. -/
def exceptionalToOrdinaryVerdictProjection (atoms : Atoms) : Projection where
  source := exceptionalAuthorityView atoms
  target := ordinaryVerdictView
  map := fun _ => (permit atoms).ordinaryVerdict

/-- Origin-bound C1 as a proof-carrying separation with an admitted
    exceptional control and the positive control of the verdict-level target
    judgment.  This does not fabricate an ordinary `AuthorizedStep`. -/
def exceptionalOrdinaryVerdictSeparation (atoms : Atoms) :
    SeparationReceipt (exceptionalToOrdinaryVerdictProjection atoms) where
  witness := nativeClaim atoms .prospective
  source_holds := ⟨⟨rfl, permit atoms, rfl⟩⟩
  image_refused := by
    intro authorized
    have denied := (ordinaryLaunderRefusal atoms).denied
    exact AuthorityVerdict.noConfusion (denied.symm.trans authorized)
  target_control := .authorized
  target_control_holds := rfl

/-- The deferred C1 boundary at the origin-bound family's native retained
    ordinary-verdict coordinate.  The historical `AuthorizedStep` theorem
    remains an adverse predecessor, not a target type smuggled into this
    independently native model. -/
theorem exceptional_permission_does_not_embed_into_authorized_verdict
    (atoms : Atoms) :
    ¬ ∀ claim : Claim,
      (governedFamily atoms).Authority claim →
        (permit atoms).ordinaryVerdict = .authorized := by
  intro embeds
  exact (exceptionalOrdinaryVerdictSeparation atoms).image_refused
    (embeds (exceptionalOrdinaryVerdictSeparation atoms).witness
      (exceptionalOrdinaryVerdictSeparation atoms).source_holds)

/-- The separation is non-vacuous on both sides and retains the native denial
    rather than inferring refusal from an empty target judgment. -/
theorem exceptional_ordinary_verdict_separation_has_nearby_controls
    (atoms : Atoms) :
    (governedFamily atoms).Authority (nativeClaim atoms .prospective) ∧
      (permit atoms).ordinaryVerdict = .denied ∧
      ordinaryVerdictView.holds .authorized :=
  ⟨(exceptionalOrdinaryVerdictSeparation atoms).source_holds,
    (ordinaryLaunderRefusal atoms).denied, rfl⟩

/-! ## Settlement standing remains separated from audit cleanliness -/

def settlementStandingView (atoms : Atoms) : JudgmentView where
  Carrier := Claim
  holds := fun claim => (governedFamily atoms).Standing claim

/-- Audit cleanliness retains the claim origin as part of the observed
    target.  A foreign claim cannot become a clean target merely because its
    phase selects an empty local snapshot. -/
def exactAuditCleanView (atoms : Atoms) : JudgmentView where
  Carrier := Claim
  holds := fun claim =>
    claim.origin = atoms.origin ∧ (claim.ledger atoms).auditTrail.Clean

def settlementStandingToAuditProjection (atoms : Atoms) : Projection where
  source := settlementStandingView atoms
  target := exactAuditCleanView atoms
  map := id

/-- Settlement standing survives at the audit-laundering claim while the
    exact retained history refuses cleanliness.  The prospective native claim
    is the nearby clean target control. -/
def settlementAuditSeparation (atoms : Atoms) :
    SeparationReceipt (settlementStandingToAuditProjection atoms) where
  witness := nativeClaim atoms .auditLaunder
  source_holds := audit_launder_has_settlement_standing atoms
  image_refused := by
    rintro ⟨_, clean⟩
    exact native_settled_history_is_not_audit_clean atoms clean
  target_control := nativeClaim atoms .prospective
  target_control_holds := by
    refine ⟨rfl, ?_⟩
    rfl

/-- Valid settlement standing is insufficient to clean the audit book.  This
    is a separate comparison from exceptional-versus-ordinary authority. -/
theorem settlement_standing_does_not_embed_into_audit_clean
    (atoms : Atoms) :
    ¬ ∀ claim : Claim,
      (governedFamily atoms).Standing claim →
        claim.origin = atoms.origin ∧
          (claim.ledger atoms).auditTrail.Clean := by
  intro embeds
  exact (settlementAuditSeparation atoms).image_refused
    (embeds (settlementAuditSeparation atoms).witness
      (settlementAuditSeparation atoms).source_holds)

/-- The exact hostile control: settlement standing is genuinely present and
    the independent ordered-history book is genuinely non-clean. -/
theorem settlement_standing_survives_while_audit_rejects
    (atoms : Atoms) :
    (governedFamily atoms).Standing (nativeClaim atoms .auditLaunder) ∧
      ¬ (finalLedger atoms).auditTrail.Clean :=
  ⟨audit_launder_has_settlement_standing atoms,
    native_settled_history_is_not_audit_clean atoms⟩

#print axioms exceptional_permission_does_not_embed_into_authorized_verdict
#print axioms exceptional_ordinary_verdict_separation_has_nearby_controls
#print axioms settlement_standing_does_not_embed_into_audit_clean
#print axioms settlement_standing_survives_while_audit_rejects

end

end Admissibility.Calculus.Instances.BreakGlass
