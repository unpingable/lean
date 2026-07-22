/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE
-/

import PJ.Core

/-!
  PJ Tranche B-prime: exact native-receipt anti-minting.

  This module adds no generic lawfulness flag and no generic frontier.  PJ-A
  already established lawfulness only for independently qualified adapters;
  arbitrary `IndexedJudgmentBridge` inhabitants remain raw substrate.

  The generic claim tested here is therefore parametric and negative: there
  is no uniform operation which, for every PJ bridge, turns independently
  inhabited source and target judgments into source-relative entitlement
  without accepting the bridge's exact native receipt.
-/

namespace PJ.TrancheBPrime

universe uSource uTarget uSourceJudgment uTargetJudgment uReceipt uOutput

/-- A bounded admissible consumer exposes no bare-target entry point.  Its
    force-bearing operation accepts the complete exact source-relative
    entitlement.  The generic layer says nothing about execution, authority,
    or success. -/
structure AdmissibleConsumer
    (bridge : PJ.IndexedJudgmentBridge)
    (source : bridge.SourceIndex) (target : bridge.TargetIndex) where
  Output : Type uOutput
  consume : bridge.EntitledFrom source target → Output

namespace AdmissibleConsumer

/-- Invoke the receipt-gated operation.  No public operation on
    `AdmissibleConsumer` accepts bare independently available target evidence. -/
def consumeEntitled
    {bridge : PJ.IndexedJudgmentBridge}
    {source : bridge.SourceIndex} {target : bridge.TargetIndex}
    (consumer : AdmissibleConsumer bridge source target)
    (entitlement : bridge.EntitledFrom source target) : consumer.Output :=
  consumer.consume entitlement

end AdmissibleConsumer

/-- A local receipt-free mint attempt for one fixed PJ bridge.  Its inputs
    deliberately include independently available target truth; its output is
    the stronger source-relative entitlement. -/
def ReceiptFreeMintAt (bridge : PJ.IndexedJudgmentBridge) : Sort _ :=
  (source : bridge.SourceIndex) →
  (target : bridge.TargetIndex) →
  bridge.SourceJudgment source →
  bridge.TargetJudgment target →
  bridge.EntitledFrom source target

/-- The prohibited *uniform* lift: one operation purporting to mint exact
    entitlement for every bridge from source evidence and accidental target
    truth, without receiving any native receipt. -/
structure ReceiptFreeMinter where
  mint :
    (bridge : PJ.IndexedJudgmentBridge.{uSource, uTarget,
      uSourceJudgment, uTargetJudgment, uReceipt}) →
      ReceiptFreeMintAt bridge

/-- Exact native refusal at one inhabited crossing defeats any purported
    receipt-free minter for that bridge.  Unlike `NotEntitledFrom` alone, the
    conclusion rules out a function which is explicitly given both source
    evidence and independently available target evidence and nevertheless
    claims to manufacture entitlement at every pair of indices. -/
theorem exact_receipt_prevents_target_minting
    {bridge : PJ.IndexedJudgmentBridge}
    {source : bridge.SourceIndex} {target : bridge.TargetIndex}
    (sourceEvidence : bridge.SourceJudgment source)
    (targetEvidence : bridge.TargetJudgment target)
    (receiptRefusal : bridge.NotEntitledFrom source target) :
    ReceiptFreeMintAt bridge → False := by
  intro alleged
  exact receiptRefusal (alleged source target sourceEvidence targetEvidence)

/-- A lossless projection of native entitlements must recover the complete
    source evidence / receipt pair, not merely a metadata label. -/
structure EntitlementProjection
    (bridge : PJ.IndexedJudgmentBridge)
    (source : bridge.SourceIndex) (target : bridge.TargetIndex) where
  Presented : Type
  present : bridge.EntitledFrom source target → Presented
  recover : Presented → bridge.EntitledFrom source target
  recover_present : (entitlement : bridge.EntitledFrom source target) →
    recover (present entitlement) = entitlement

namespace EntitlementProjection

/-- Native entitlement identity cannot be silently erased by any projection
    carrying the required constructive recovery law. -/
theorem present_injective
    {bridge : PJ.IndexedJudgmentBridge}
    {source : bridge.SourceIndex} {target : bridge.TargetIndex}
    (projection : EntitlementProjection bridge source target) :
    Function.Injective projection.present := by
  intro first second equalPresentation
  calc
    first = projection.recover (projection.present first) :=
      (projection.recover_present first).symm
    _ = projection.recover (projection.present second) :=
      congrArg projection.recover equalPresentation
    _ = second := projection.recover_present second

end EntitlementProjection

/-! ## Exact index hostile

    Context and subject are components of the actual PJ source and target
    indices.  They are not parallel metadata.  Both judgment families are
    inhabited at every index; only the native receipt distinguishes lawful
    crossings.
-/

namespace Hostile

structure RequestIndex where
  context : Bool
  subject : Bool
  deriving DecidableEq

structure SourceEvidence (index : RequestIndex) where
  observed : RequestIndex
  exact : observed = index

structure TargetEvidence (index : RequestIndex) where
  observed : RequestIndex
  exact : observed = index

/-- The first genuine bridge preserves the complete context/subject index. -/
def exactIndexBridge : PJ.IndexedJudgmentBridge where
  SourceIndex := RequestIndex
  TargetIndex := RequestIndex
  SourceJudgment := SourceEvidence
  TargetJudgment := TargetEvidence
  Receipt := fun source target => source = target
  carry := by
    intro source target receipt sourceEvidence
    cases receipt
    exact ⟨sourceEvidence.observed, sourceEvidence.exact⟩

def flipContext (index : RequestIndex) : RequestIndex :=
  ⟨!index.context, index.subject⟩

/-- The second genuine bridge has a different receipt family and different
    native force: it flips context while preserving subject. -/
def contextFlipBridge : PJ.IndexedJudgmentBridge where
  SourceIndex := RequestIndex
  TargetIndex := RequestIndex
  SourceJudgment := SourceEvidence
  TargetJudgment := TargetEvidence
  Receipt := fun source target => flipContext source = target
  carry := by
    intro source target receipt sourceEvidence
    cases receipt
    exact ⟨flipContext sourceEvidence.observed,
      congrArg flipContext sourceEvidence.exact⟩

def baseIndex : RequestIndex := ⟨false, false⟩
def wrongContextIndex : RequestIndex := ⟨true, false⟩
def wrongSubjectIndex : RequestIndex := ⟨false, true⟩

def sourceAt (index : RequestIndex) : SourceEvidence index := ⟨index, rfl⟩
def targetAt (index : RequestIndex) : TargetEvidence index := ⟨index, rfl⟩

/-- Wrong context is a native receipt refusal even though source and target
    judgments are both inhabited. -/
theorem wrong_context_remains_not_entitled :
    Nonempty (exactIndexBridge.SourceJudgment baseIndex) ∧
    Nonempty (exactIndexBridge.TargetJudgment wrongContextIndex) ∧
    exactIndexBridge.NotEntitledFrom baseIndex wrongContextIndex := by
  refine ⟨⟨sourceAt baseIndex⟩, ⟨targetAt wrongContextIndex⟩, ?_⟩
  intro entitlement
  have contextEquality : false = true :=
    congrArg RequestIndex.context entitlement.receipt
  cases contextEquality

/-- Wrong subject is independently refused by the same full-index receipt
    family; it is not reduced to wrong context. -/
theorem wrong_subject_remains_not_entitled :
    Nonempty (exactIndexBridge.SourceJudgment baseIndex) ∧
    Nonempty (exactIndexBridge.TargetJudgment wrongSubjectIndex) ∧
    exactIndexBridge.NotEntitledFrom baseIndex wrongSubjectIndex := by
  refine ⟨⟨sourceAt baseIndex⟩, ⟨targetAt wrongSubjectIndex⟩, ?_⟩
  intro entitlement
  have subjectEquality : false = true :=
    congrArg RequestIndex.subject entitlement.receipt
  cases subjectEquality

/-- No universe-level uniform receipt-free minter exists.  Applying one to
    the exact-index bridge at the wrong-context crossing produces the native
    equality receipt which the hostile refutes.  Both source and target inputs
    are consumed in the application; neither judgment is empty. -/
theorem no_uniform_receipt_free_minter :
    ReceiptFreeMinter.{0, 0, 1, 1, 0} → False := by
  intro alleged
  exact exact_receipt_prevents_target_minting
    (sourceAt baseIndex) (targetAt wrongContextIndex)
    wrong_context_remains_not_entitled.2.2 (alleged.mint exactIndexBridge)

/-- Positive exact entitlement for the identity-preserving bridge. -/
def exactEntitlement :
    exactIndexBridge.EntitledFrom baseIndex baseIndex :=
  ⟨sourceAt baseIndex, rfl⟩

def exactConsumer : AdmissibleConsumer exactIndexBridge baseIndex baseIndex where
  Output := RequestIndex
  consume := fun entitlement => entitlement.targetEvidence.observed

/-- The exact positive consumer uses `targetEvidence`, hence the native
    receipt and `carry`, and recovers the requested target index. -/
theorem exact_receipt_is_sufficient_for_bounded_consumer :
    exactConsumer.consumeEntitled exactEntitlement = baseIndex := rfl

/-- Positive exact entitlement for the genuinely different context-flip
    bridge. -/
def flippedEntitlement :
    contextFlipBridge.EntitledFrom baseIndex (flipContext baseIndex) :=
  ⟨sourceAt baseIndex, rfl⟩

/-- The two bridges have observably different native force, not decorative
    bridge labels. -/
theorem distinct_native_bridges_have_distinct_force :
    exactEntitlement.targetEvidence.observed = baseIndex ∧
    flippedEntitlement.targetEvidence.observed = flipContext baseIndex :=
  ⟨rfl, rfl⟩

/-- The context-flip crossing has an exact native entitlement, while the
    identity-preserving bridge refuses that very same source/target pair.
    Thus actual bridge values and their receipt families, not decorative
    labels, are non-interchangeable. -/
theorem wrong_native_bridge_remains_not_interchangeable :
    Nonempty
      (contextFlipBridge.EntitledFrom baseIndex (flipContext baseIndex)) ∧
    exactIndexBridge.NotEntitledFrom baseIndex (flipContext baseIndex) := by
  refine ⟨⟨flippedEntitlement⟩, ?_⟩
  intro entitlement
  have contextEquality : false = true :=
    congrArg RequestIndex.context entitlement.receipt
  cases contextEquality

/-! ### Collapse attack

    Replacing the dependent receipt family with `Unit` makes a local
    receipt-free mint operation constructible.  This positive attack shows
    that exact native receipt indexing, rather than grander terminology, is
    load-bearing in the negative result.
-/

def collapsedBridge : PJ.IndexedJudgmentBridge where
  SourceIndex := RequestIndex
  TargetIndex := RequestIndex
  SourceJudgment := fun _ => Unit
  TargetJudgment := fun _ => Unit
  Receipt := fun _ _ => Unit
  carry := fun _ _ => ()

def collapsed_bridge_admits_receipt_free_mint :
    ReceiptFreeMintAt collapsedBridge :=
  fun _source _target sourceEvidence _targetTruth =>
    ⟨sourceEvidence, ()⟩

/-! ### Native receipt identity erasure

    These entitlements share source, target, and source evidence.  Their
    native receipts are force-bearing and yield different target evidence.
-/

def forceBearingBridge : PJ.IndexedJudgmentBridge where
  SourceIndex := Unit
  TargetIndex := Unit
  SourceJudgment := fun _ => Unit
  TargetJudgment := fun _ => Bool
  Receipt := fun _ _ => Bool
  carry := fun receipt _ => receipt

def falseForceEntitlement : forceBearingBridge.EntitledFrom () () :=
  ⟨(), false⟩

def trueForceEntitlement : forceBearingBridge.EntitledFrom () () :=
  ⟨(), true⟩

private theorem forceEntitlementsDistinct :
    falseForceEntitlement ≠ trueForceEntitlement := by
  intro equality
  have targetEquality : false = true :=
    congrArg PJ.IndexedJudgmentBridge.EntitledFrom.targetEvidence equality
  cases targetEquality

/-- Erasing the complete native entitlement to `Unit` cannot admit an exact
    recovery map.  This attacks receipt erasure itself, not a parallel token.
-/
theorem native_receipt_erasure_has_no_left_inverse :
    ¬ ∃ recover : Unit → forceBearingBridge.EntitledFrom () (),
      (entitlement : forceBearingBridge.EntitledFrom () ()) →
        recover () = entitlement := by
  intro alleged
  obtain ⟨recover, recovers⟩ := alleged
  apply forceEntitlementsDistinct
  calc
    falseForceEntitlement = recover () :=
      (recovers falseForceEntitlement).symm
    _ = trueForceEntitlement := recovers trueForceEntitlement

#print axioms wrong_context_remains_not_entitled
#print axioms wrong_subject_remains_not_entitled
#print axioms no_uniform_receipt_free_minter
#print axioms exact_receipt_is_sufficient_for_bounded_consumer
#print axioms distinct_native_bridges_have_distinct_force
#print axioms wrong_native_bridge_remains_not_interchangeable
#print axioms collapsed_bridge_admits_receipt_free_mint
#print axioms native_receipt_erasure_has_no_left_inverse

end Hostile

#print axioms AdmissibleConsumer.consumeEntitled
#print axioms exact_receipt_prevents_target_minting
#print axioms EntitlementProjection.present_injective

end PJ.TrancheBPrime
