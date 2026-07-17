/-
  LeanProofs.CustodyIndexed.OverlapAudits -- C3 kernel-overlap audit runs (the
  anti-fake-mustache machine, docs/POST-V4-CAMPAIGN.md C3).

  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: STABLE-SURFACE
  This module is part of the exact `LeanProofs.CustodyIndexed` stable root.

  WHAT A C3 RUN IS: a candidate primitive (from the doctrine kitchen /
  laundering-move watchlist) is instantiated as a `System` and its claimed
  wall is checked against the resident kernel. The output is an AUDIT
  VERDICT, not a kernel: either the wall is an INSTANCE of a resident
  theorem/mechanism (deflate -- cite, do not re-mint), or a precisely-named
  delta remains (record it; formalize it when its statement, overlap boundary,
  and anti-vacuity witness are fixed). A consumer is not an admission gate.
  Verdicts are recorded per-section and mirrored in the campaign changelog.

  ## Run 1 — relation-promotion (derived-relations-need-witnesses)

  Candidate: papers `working/tooltheory/derived-relations-need-witnesses.md`
  (CANDIDATE/NON-BINDING, 2026-06-19). Law: a derived relation may NOT be
  promoted from the conjunction of its endpoints' receipts; the relation
  needs its own admitted witness, else `cannot_testify`.

  VERDICT (two-sided; the verdict sentences are META-VERDICTS -- audit
  judgments supported by, not identical to, the named theorems):
  * WALL FACE = INSTANCE, twice over. "Relation underivable without its own
    receipt" is (i) the receipt-rooted underivability pattern (Zoo
    mechanism 5 / the `no_evidence_synthesis` genus) -- proved as
    `relation_requires_relation_receipt`; and (ii) with the evidence indices
    kept honest (endpoint-evidence ≠ relation-evidence, `iEndpointEvid` vs
    `iRelEvid` -- a codex audit caught the first draft flattening them), an
    instance of the resident INDEX-CLOSURE machinery: the clean system is
    closed over the relation-free index set, so the relation is underivable
    by `no_free_cross_cut_generic` (`relation_wall_is_closure_instance`).
  * ATTACK FACE = NOT CAUGHT BY ANY RESIDENT SCREEN, and the closure
    analysis says exactly where the would-be screen lives. Proved support:
    the promotion family SATISFIES `EvidenceNeverConcluded`
    (`promote_discipline`); its evidence is no universal stamp
    (`promote_not_universal` -- the one resident screen statable here;
    crossroads needs hub mediation absent by shape, caveat-blind is
    caveat-vocabulary); and promotion is a CLOSURE VIOLATION
    (`promote_breaks_closure`): premises inside the relation-free set,
    conclusion outside. So the would-be screen is an index-typed
    evidence-jurisdiction condition ("relation-indexed judgments conclude
    only from relation-indexed evidence") -- an instance of the closure
    GENUS whose screen predicate is NOT minted here: its exact statement and
    overlap boundary remain open. The remaining un-owned delta
    (`cannot_testify` as an output VERDICT type, distinct from mere
    underivability) is outside the derivability vocabulary entirely. No
    consumer is required to formalize either result once its shape is fixed.

  ## Run 2 — silence-as-denial (signal-authority)

  Candidate: the signal-authority primitive (missing ACK ≠ NACK; Lean
  deferred). Protocol face already resident as a Boolean specimen
  (`AuthenticatedDenial.lean`: silence ↛ denial, signed denial = paid path).

  VERDICT: CAUGHT BY RESIDENT MECHANISM. In sequent form the timeout record
  is CONCLUDED (by the probe) and the attack cites it as EVIDENCE of denial
  -- discipline unsatisfiability, the summary-as-authority mechanism
  (Zoo mechanism 3), two lines (`silence_as_denial_violates_discipline`).
  The wall face is the same receipt-rooted instance as Run 1. No new cage
  family needed; `AuthenticatedDenial` remains the protocol-face home; this
  section is the sequent-face audit record.

  Mathlib-free.
-/

import LeanProofs.CustodyIndexed.EvidenceCalculusSequent

namespace LeanProofs.CustodyIndexed.OverlapAudits

open LeanProofs.CustodyIndexed.CustodyIndexedSequent (System IsEvidence
  EvidenceNeverConcluded Entail entail_iff_rooted no_free_cross_cut_generic)
open LeanProofs.CustodyIndexed.EvidenceCalculusSequent (Fundable UniversalStamp)

/-! ## Run 1: relation-promotion -/

section RelationPromotion

inductive RJ where
  | endpointsPair | receiptA | receiptB | relationReceipt
  | verdictA | verdictB | relationJ
  deriving DecidableEq

/-- Index vocabulary keeps endpoint evidence and relation evidence DISTINCT
    (`iEndpointEvid` ≠ `iRelEvid`): the audit's closure analysis depends on
    the distinction being expressible, and flattening them (first draft)
    hides the resident machinery that speaks to this candidate. -/
inductive RIx where
  | iPair | iVerdict | iRel | iEndpointEvid | iRelEvid
  deriving DecidableEq

def rjix : RJ → RIx
  | .endpointsPair => .iPair
  | .receiptA => .iEndpointEvid
  | .receiptB => .iEndpointEvid
  | .relationReceipt => .iRelEvid
  | .verdictA => .iVerdict
  | .verdictB => .iVerdict
  | .relationJ => .iRel

/-- The CLEAN system: endpoint receipts fund endpoint verdicts; the relation
    is concluded only from its OWN admitted witness. -/
inductive CleanRelationRule : RJ → RJ → RJ → Prop where
  | vA : CleanRelationRule .endpointsPair .receiptA .verdictA
  | vB : CleanRelationRule .endpointsPair .receiptB .verdictB
  | relate : CleanRelationRule .endpointsPair .relationReceipt .relationJ

def cleanRelationSystem : System RJ RIx :=
  { ix := rjix, Rule := CleanRelationRule }

theorem clean_relation_discipline :
    EvidenceNeverConcluded cleanRelationSystem := by
  intro _ _ _ hr _ _ hr'
  cases hr <;> cases hr'

/-- The general wall (INSTANCE of the receipt-rooted pattern -- cite, don't
    re-mint): without the relation's own receipt, the relation judgment is
    underivable at any depth. -/
theorem relation_requires_relation_receipt {Γ : List RJ}
    (hrec : RJ.relationReceipt ∉ Γ) (hout : RJ.relationJ ∉ Γ) :
    ¬ Entail cleanRelationSystem Γ RJ.relationJ := by
  intro h
  cases (entail_iff_rooted clean_relation_discipline).mp h with
  | ax hmem => exact hout hmem
  | cut r _ hevid =>
      cases r with
      | relate => exact hrec hevid

/-- **The candidate's law, replayed**: both endpoint verdicts derivable, the
    relation NOT -- verdict(A) ∧ verdict(B) does not explain A-vs-B. The
    honest output about the difference is refusal. -/
theorem endpoint_verdicts_do_not_yield_relation :
    Entail cleanRelationSystem [RJ.endpointsPair, RJ.receiptA, RJ.receiptB]
      RJ.verdictA ∧
    Entail cleanRelationSystem [RJ.endpointsPair, RJ.receiptA, RJ.receiptB]
      RJ.verdictB ∧
    ¬ Entail cleanRelationSystem [RJ.endpointsPair, RJ.receiptA, RJ.receiptB]
      RJ.relationJ :=
  ⟨Entail.cut CleanRelationRule.vA
      (Entail.ax (List.Mem.head _))
      (Entail.ax (List.Mem.tail _ (List.Mem.head _))),
    Entail.cut CleanRelationRule.vB
      (Entail.ax (List.Mem.head _))
      (Entail.ax (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))),
    relation_requires_relation_receipt
      (fun h => by cases h with
        | tail _ h' => cases h' with
          | tail _ h'' => cases h'' with
            | tail _ h3 => cases h3)
      (fun h => by cases h with
        | tail _ h' => cases h' with
          | tail _ h'' => cases h'' with
            | tail _ h3 => cases h3)⟩

/-- FORBIDDEN SPECIMEN (audit object): the clean system plus the promotion
    FAMILY -- the relation concluded directly from the two endpoint
    receipts, no relation witness. Both orderings are included: the binary
    cut puts one receipt in source position, and that src/evid asymmetry is
    an encoding artifact (codex-flagged), not load-bearing -- the verdict is
    identical under either assignment. True minimal pair: clean rules
    retained unchanged, ONE family added. -/
inductive PromoteRule : RJ → RJ → RJ → Prop where
  | vA : PromoteRule .endpointsPair .receiptA .verdictA
  | vB : PromoteRule .endpointsPair .receiptB .verdictB
  | relate : PromoteRule .endpointsPair .relationReceipt .relationJ
  | promote : PromoteRule .receiptA .receiptB .relationJ
  | promoteSym : PromoteRule .receiptB .receiptA .relationJ

def promoteSystem : System RJ RIx :=
  { ix := rjix, Rule := PromoteRule }

/-- The promotion works in the attack system: the relation is derivable from
    the endpoint receipts alone -- this is what the candidate refuses. -/
theorem promote_system_promotes :
    Entail promoteSystem [RJ.endpointsPair, RJ.receiptA, RJ.receiptB]
      RJ.relationJ :=
  Entail.cut PromoteRule.promote
    (Entail.ax (List.Mem.tail _ (List.Mem.head _)))
    (Entail.ax (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

/-- **The audit's load-bearing negative: the attack SATISFIES the custody
    discipline.** No evidence judgment is ever concluded -- `promote` is
    well-typed custody. The discipline-unsatisfiability mechanism cannot
    catch relation-promotion. -/
theorem promote_discipline : EvidenceNeverConcluded promoteSystem := by
  intro _ _ _ hr _ _ hr'
  cases hr <;> cases hr'

/-- Nor is the promoting evidence a universal stamp: `receiptB` cannot fund
    the endpoint verdict `verdictA`. The currency screen does not catch
    promotion either. (Narrow by design: the other resident screens are not
    statable in this vocabulary -- see the header meta-verdict.) -/
theorem promote_not_universal :
    ¬ UniversalStamp promoteSystem RJ.receiptB := fun h =>
  nomatch (h RJ.endpointsPair RJ.verdictA ⟨RJ.receiptA, PromoteRule.vA⟩)

/-- The relation-free index set: everything except the relation judgment
    and the relation's own evidence species. -/
def RelFree : RIx → Prop := fun i => i ≠ RIx.iRel ∧ i ≠ RIx.iRelEvid

/-- **The wall as a closure instance** (second resident citation): the
    clean system is rule-closed over the relation-free indices, so the
    relation judgment is underivable from the endpoint context by the
    resident generic `no_free_cross_cut_generic` -- no new proof needed. -/
theorem relation_wall_is_closure_instance :
    ¬ Entail cleanRelationSystem
        [RJ.endpointsPair, RJ.receiptA, RJ.receiptB] RJ.relationJ := by
  refine no_free_cross_cut_generic (C := RelFree) ?_ ?_ ?_
  · intro src evid tgt hr hsrc hevid
    cases hr with
    | vA => exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
    | vB => exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
    | relate => exact absurd rfl hevid.2
  · intro j hj
    cases hj with
    | head => exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
    | tail _ h1 =>
        cases h1 with
        | head => exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
        | tail _ h2 =>
            cases h2 with
            | head => exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
            | tail _ h3 => cases h3
  · intro hC
    exact hC.1 rfl

/-- **Promotion is a closure violation**: the promote rule's premises are
    relation-free, its conclusion is not -- the exact shape the would-be
    screen (an evidence-jurisdiction condition of the closure genus) would
    inspect for. Not minted as a screen; recorded as the audit's
    where-it-would-live witness. -/
theorem promote_breaks_closure :
    ∃ (src evid tgt : RJ), promoteSystem.Rule src evid tgt ∧
      RelFree (promoteSystem.ix src) ∧ RelFree (promoteSystem.ix evid) ∧
      ¬ RelFree (promoteSystem.ix tgt) :=
  ⟨RJ.receiptA, RJ.receiptB, RJ.relationJ, PromoteRule.promote,
    ⟨(fun h => nomatch h), (fun h => nomatch h)⟩,
    ⟨(fun h => nomatch h), (fun h => nomatch h)⟩,
    fun hC => hC.1 rfl⟩

end RelationPromotion

/-! ## Run 2: silence-as-denial -/

section SilenceAsDenial

inductive NJ where
  | query | proberCred | timeoutRec | signedDenial | deniedJ
  deriving DecidableEq

inductive NIx where
  | iQuery | iRecord | iDenial | iEvid
  deriving DecidableEq

def njix : NJ → NIx
  | .query => .iQuery
  | .proberCred => .iEvid
  | .timeoutRec => .iRecord
  | .signedDenial => .iEvid
  | .deniedJ => .iDenial

/-- The CLEAN system: probing concludes the timeout RECORD; denial is
    concluded only from an authority-signed denial witness. -/
inductive CleanDenialRule : NJ → NJ → NJ → Prop where
  | probe : CleanDenialRule .query .proberCred .timeoutRec
  | deny : CleanDenialRule .query .signedDenial .deniedJ

def cleanDenialSystem : System NJ NIx :=
  { ix := njix, Rule := CleanDenialRule }

theorem clean_denial_discipline :
    EvidenceNeverConcluded cleanDenialSystem := by
  intro _ _ _ hr _ _ hr'
  cases hr <;> cases hr'

/-- The general wall (INSTANCE, same genus as Run 1): without a signed
    denial witness, denial is underivable at any depth. -/
theorem denial_requires_signed_witness {Γ : List NJ}
    (hrec : NJ.signedDenial ∉ Γ) (hout : NJ.deniedJ ∉ Γ) :
    ¬ Entail cleanDenialSystem Γ NJ.deniedJ := by
  intro h
  cases (entail_iff_rooted clean_denial_discipline).mp h with
  | ax hmem => exact hout hmem
  | cut r _ hevid =>
      cases r with
      | deny => exact hrec hevid

/-- **The wall replay**: the timeout IS recorded, the denial is NOT
    concluded -- silence is absence of information. -/
theorem silence_records_without_denying :
    Entail cleanDenialSystem [NJ.query, NJ.proberCred] NJ.timeoutRec ∧
    ¬ Entail cleanDenialSystem [NJ.query, NJ.proberCred] NJ.deniedJ :=
  ⟨Entail.cut CleanDenialRule.probe
      (Entail.ax (List.Mem.head _))
      (Entail.ax (List.Mem.tail _ (List.Mem.head _))),
    denial_requires_signed_witness
      (fun h => by cases h with
        | tail _ h' => cases h' with
          | tail _ h'' => cases h'')
      (fun h => by cases h with
        | tail _ h' => cases h' with
          | tail _ h'' => cases h'')⟩

/-- FORBIDDEN SPECIMEN (audit object): the clean system plus ONE rule -- the
    timeout record cited as evidence of denial. True minimal pair: nothing
    dropped. -/
inductive SilenceAsDenialRule : NJ → NJ → NJ → Prop where
  | probe : SilenceAsDenialRule .query .proberCred .timeoutRec
  | deny : SilenceAsDenialRule .query .signedDenial .deniedJ
  | silenceDenies : SilenceAsDenialRule .query .timeoutRec .deniedJ

def silenceAsDenialSystem : System NJ NIx :=
  { ix := njix, Rule := SilenceAsDenialRule }

/-- **The audit's positive verdict: the resident mechanism catches it.** The
    timeout record is both CONCLUDED (by the probe) and cited as EVIDENCE
    (by the attack rule) -- discipline unsatisfiable, exactly the
    summary-as-authority catch. No new cage family needed. -/
theorem silence_as_denial_violates_discipline :
    ¬ EvidenceNeverConcluded silenceAsDenialSystem := by
  intro hD
  exact hD SilenceAsDenialRule.silenceDenies SilenceAsDenialRule.probe

end SilenceAsDenial

end LeanProofs.CustodyIndexed.OverlapAudits
