/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE
-/

/-!
  PJ provisional cross-calculus substrate.

  An `IndexedJudgmentBridge` is one oriented rule between two independently
  indexed evidence families.  Its receipt is bound to the exact source and
  target indices.  Bare target evidence and source-relative entitlement are
  deliberately different objects.

  This signature contains no generic composition, identity, refusal sum,
  owner, authority, custody, spend, frontier, or context-transport law.
-/

namespace PJ

universe uSource uTarget uSourceJudgment uTargetJudgment uReceipt

/-- One evidence-bearing, index-bound bridge rule.  `carry` is the native rule
    supplied by an instance; it is not an assertion that an arbitrary bridge
    is allowed. -/
structure IndexedJudgmentBridge where
  SourceIndex : Type uSource
  TargetIndex : Type uTarget
  SourceJudgment : SourceIndex → Sort uSourceJudgment
  TargetJudgment : TargetIndex → Sort uTargetJudgment
  Receipt : SourceIndex → TargetIndex → Sort uReceipt
  carry : {source : SourceIndex} → {target : TargetIndex} →
    Receipt source target → SourceJudgment source → TargetJudgment target

namespace IndexedJudgmentBridge

/-- Exact source-relative entitlement retains both the source evidence and the
    native receipt.  It intentionally does not store the target conclusion. -/
structure EntitledFrom (bridge : IndexedJudgmentBridge)
    (source : bridge.SourceIndex) (target : bridge.TargetIndex) where
  sourceEvidence : bridge.SourceJudgment source
  receipt : bridge.Receipt source target

/-- Consume a source-relative entitlement through the instance's exact native
    rule. -/
def EntitledFrom.targetEvidence
    {bridge : IndexedJudgmentBridge}
    {source : bridge.SourceIndex} {target : bridge.TargetIndex}
    (entitled : bridge.EntitledFrom source target) :
    bridge.TargetJudgment target :=
  bridge.carry entitled.receipt entitled.sourceEvidence

/-- Exact anti-entitlement is the constructive absence of a source-evidence /
    receipt pair.  It is not target falsity: the target judgment may be
    independently inhabited. -/
def NotEntitledFrom (bridge : IndexedJudgmentBridge)
    (source : bridge.SourceIndex) (target : bridge.TargetIndex) : Prop :=
  bridge.EntitledFrom source target → False

end IndexedJudgmentBridge

#print axioms IndexedJudgmentBridge.EntitledFrom.targetEvidence

end PJ
