/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE
-/

import PJ.TrancheBPrime.AntiMinting

/-!
  PJ Tranche D-prime: independent collapse attacks against the PJ-A core and
  the B-prime exact-receipt anti-minting layer.

  These fixtures do not revise either ratified layer.  They locate the exact
  load-bearing boundary:

  * the bare PJ core accepts context-erasing, subject-erasing, constant, and
    otherwise unqualified bridges;
  * an `AdmissibleConsumer` can ignore its entitlement;
  * any family of freely supplied receipts constructs a receipt-free minter;
  * at one inhabited source/target pair, receipt-free minting is
    constructively equivalent to inhabitation of the exact entitlement;
  * B-prime becomes scientifically discriminating only when a source adapter
    independently supplies a native, index-sensitive receipt refusal.

  Thus the hostile audit preserves B-prime's narrow no-uniform-mint result,
  while refusing to reinterpret it as generic bridge qualification,
  unforgeability, institutional enforcement, or functional receipt use.
-/

namespace PJ.TrancheDPrime.CollapseHostiles

open PJ.IndexedJudgmentBridge
open PJ.TrancheBPrime
open PJ.TrancheBPrime.Hostile

universe uSource uTarget uSourceJudgment uTargetJudgment uReceipt

/-! ## Collapse of the generic anti-minting surface -/

/-- A fixed-pair variant makes the logical boundary explicit.  Unlike
    B-prime's total `ReceiptFreeMintAt`, it asks only about one crossing. -/
def FixedReceiptFreeMintAt
    (bridge : PJ.IndexedJudgmentBridge)
    (source : bridge.SourceIndex) (target : bridge.TargetIndex) : Sort _ :=
  bridge.SourceJudgment source →
    bridge.TargetJudgment target →
      bridge.EntitledFrom source target

/-- When source and target judgments are independently inhabited, a
    fixed-pair receipt-free minter is equivalent merely to inhabitation of the
    exact entitlement.  Consequently the generic layer does not add a second
    notion of lawfulness at one crossing; all discrimination comes from the
    native receipt family supplied by the instance. -/
theorem fixed_mint_iff_exact_entitlement_inhabited
    {bridge : PJ.IndexedJudgmentBridge}
    {source : bridge.SourceIndex} {target : bridge.TargetIndex}
    (sourceEvidence : bridge.SourceJudgment source)
    (targetEvidence : bridge.TargetJudgment target) :
    Nonempty (FixedReceiptFreeMintAt bridge source target) ↔
      Nonempty (bridge.EntitledFrom source target) := by
  constructor
  · rintro ⟨mint⟩
    exact ⟨mint sourceEvidence targetEvidence⟩
  · rintro ⟨entitlement⟩
    exact ⟨fun _source _target => entitlement⟩

/-- A freely selectable native receipt is enough to construct B-prime's
    total receipt-free minter.  Target truth is accepted as an argument but
    is not load-bearing.  B-prime therefore rules out such a minter only when
    an instance exhibits a genuinely empty native receipt fiber. -/
def receiptsEverywhereGiveMint
    {bridge : PJ.IndexedJudgmentBridge.{uSource, uTarget,
      uSourceJudgment, uTargetJudgment, uReceipt}}
    (chooseReceipt : (source : bridge.SourceIndex) →
      (target : bridge.TargetIndex) → bridge.Receipt source target) :
    ReceiptFreeMintAt bridge :=
  fun source target sourceEvidence _targetTruth =>
    ⟨sourceEvidence, chooseReceipt source target⟩

/-- Even B-prime's force-bearing Bool-receipt fixture admits a total closed
    minter: choose one of its native receipts.  Proof-relevant receipt
    identity alone is not anti-minting; an exact refused receipt fiber is the
    load-bearing local fact. -/
def force_bearing_receipts_still_admit_total_mint :
    ReceiptFreeMintAt forceBearingBridge :=
  receiptsEverywhereGiveMint (fun _source _target => false)

/-! ## Collapse of context and subject indices -/

/-- This raw PJ bridge preserves only subject and erases context.  Its carry
    operation may construct target evidence at the requested target directly.
    The PJ-A signature accepts it because semantic bridge qualification is
    intentionally external to the common core. -/
def contextErasedBridge : PJ.IndexedJudgmentBridge where
  SourceIndex := RequestIndex
  TargetIndex := RequestIndex
  SourceJudgment := SourceEvidence
  TargetJudgment := TargetEvidence
  Receipt := fun source target => source.subject = target.subject
  carry := fun _receipt _sourceEvidence => ⟨_, rfl⟩

def contextErasedEntitlement :
    contextErasedBridge.EntitledFrom baseIndex wrongContextIndex :=
  ⟨sourceAt baseIndex, rfl⟩

/-- Erasing context admits exactly the crossing refused by the native
    exact-index bridge. -/
theorem erased_context_mints_previously_refused_crossing :
    exactIndexBridge.NotEntitledFrom baseIndex wrongContextIndex ∧
      Nonempty
        (contextErasedBridge.EntitledFrom baseIndex wrongContextIndex) :=
  ⟨wrong_context_remains_not_entitled.2.2, ⟨contextErasedEntitlement⟩⟩

/-- The dual raw bridge preserves only context and erases subject. -/
def subjectErasedBridge : PJ.IndexedJudgmentBridge where
  SourceIndex := RequestIndex
  TargetIndex := RequestIndex
  SourceJudgment := SourceEvidence
  TargetJudgment := TargetEvidence
  Receipt := fun source target => source.context = target.context
  carry := fun _receipt _sourceEvidence => ⟨_, rfl⟩

def subjectErasedEntitlement :
    subjectErasedBridge.EntitledFrom baseIndex wrongSubjectIndex :=
  ⟨sourceAt baseIndex, rfl⟩

/-- Erasing subject independently admits the second crossing refused by the
    native exact-index bridge. -/
theorem erased_subject_mints_previously_refused_crossing :
    exactIndexBridge.NotEntitledFrom baseIndex wrongSubjectIndex ∧
      Nonempty
        (subjectErasedBridge.EntitledFrom baseIndex wrongSubjectIndex) :=
  ⟨wrong_subject_remains_not_entitled.2.2, ⟨subjectErasedEntitlement⟩⟩

/-! ## Consumer and qualification collapse -/

/-- Receipt gating does not imply functional use of receipt identity.  This
    perfectly valid bounded consumer returns one constant result for both
    force-bearing Bool receipts. -/
def receiptIgnoringConsumer :
    AdmissibleConsumer forceBearingBridge () () where
  Output := Unit
  consume := fun _entitlement => ()

/-- Two distinct exact entitlements are observationally collapsed by the
    same admissible consumer. -/
theorem admissible_consumer_need_not_use_receipt_identity :
    receiptIgnoringConsumer.consumeEntitled falseForceEntitlement =
      receiptIgnoringConsumer.consumeEntitled trueForceEntitlement :=
  rfl

/-- The raw collapsed bridge is accepted by the same consumer interface even
    though its Unit receipt already admits B-prime's receipt-free mint.  This
    is a constructive witness that `AdmissibleConsumer` does not itself check
    the campaign-external adapter qualification. -/
def rawCollapsedConsumer :
    AdmissibleConsumer collapsedBridge baseIndex wrongContextIndex where
  Output := Unit
  consume := fun _entitlement => ()

def rawCollapsedEntitlement :
    collapsedBridge.EntitledFrom baseIndex wrongContextIndex :=
  collapsed_bridge_admits_receipt_free_mint
    baseIndex wrongContextIndex () ()

theorem unqualified_raw_bridge_enters_consumer :
    rawCollapsedConsumer.consumeEntitled rawCollapsedEntitlement = () :=
  rfl

/-! ## Audit disposition encoded by the fixtures

  The collapse attacks do not refute the exact local refusals or the theorem
  that one such refusal defeats a total minter.  They do refute stronger
  readings: the common core does not qualify bridges, make receipts
  unforgeable, preserve arbitrary indices, enforce receipt use, or supply an
  institution.  Those facts remain adapter-local.
-/

#print axioms fixed_mint_iff_exact_entitlement_inhabited
#print axioms receiptsEverywhereGiveMint
#print axioms force_bearing_receipts_still_admit_total_mint
#print axioms contextErasedEntitlement
#print axioms erased_context_mints_previously_refused_crossing
#print axioms subjectErasedEntitlement
#print axioms erased_subject_mints_previously_refused_crossing
#print axioms admissible_consumer_need_not_use_receipt_identity
#print axioms rawCollapsedEntitlement
#print axioms unqualified_raw_bridge_enters_consumer

end PJ.TrancheDPrime.CollapseHostiles
