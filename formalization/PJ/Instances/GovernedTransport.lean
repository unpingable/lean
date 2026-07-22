/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE
-/

import PJ.Core
import LeanProofs.GovernedTransport.Core
import LeanProofs.GovernedTransport.Positive
import LeanProofs.GovernedTransport.Negative
import LeanProofs.GovernedTransportEvidence.Hostile

/-!
  Faithful PJ adapter for the ratified Governed Transport core.

  Each native GT edge becomes one `PJ.IndexedJudgmentBridge`.  Translation
  and target-local reliance remain two different bridge values; this module
  deliberately does not manufacture a composite bridge, generic coverage,
  or target authority.
-/

namespace PJ.Instances.GovernedTransport

open LeanProofs.GovernedTransport

universe u v w p q r

/-- The exact receipt for one GT translation edge.  It retains the native
    crossing witness and proves both endpoint bindings. -/
structure RouteReceipt
    {Source : Type u} {Target : Type v}
    (bridge : Span.{u, v, w} Source Target)
    (source : Source) (target : Target) where
  crossing : bridge.Witness
  source_eq : bridge.source crossing = source
  target_eq : bridge.target crossing = target

/-- One native positive translation edge, without target-local reliance. -/
def positiveTranslationBridge
    {Source : Type u} {Target : Type v}
    {bridge : Span.{u, v, w} Source Target}
    {SourcePositive : Source → Type p}
    {ImportedPositive : Target → Type q}
    (translate : TranslateAlong bridge SourcePositive ImportedPositive) :
    PJ.IndexedJudgmentBridge where
  SourceIndex := Source
  TargetIndex := Target
  SourceJudgment := SourcePositive
  TargetJudgment := ImportedPositive
  Receipt := RouteReceipt bridge
  carry := by
    intro source target receipt positive
    exact receipt.target_eq ▸
      translate receipt.crossing (receipt.source_eq.symm ▸ positive)

/-- One native positive target-local reliance edge.  Its equality receipt
    records that reliance is exercised at the same target candidate; it is
    not supplied by the preceding translation receipt. -/
def positiveRelianceBridge
    {Target : Type v}
    {ImportedPositive : Target → Type q}
    {TargetPositive : Target → Type r}
    (rely : RelyLocally ImportedPositive TargetPositive) :
    PJ.IndexedJudgmentBridge where
  SourceIndex := Target
  TargetIndex := Target
  SourceJudgment := ImportedPositive
  TargetJudgment := TargetPositive
  Receipt importedTarget localTarget := importedTarget = localTarget
  carry := by
    intro importedTarget localTarget sameTarget imported
    exact sameTarget ▸ rely importedTarget imported

/-- One native negative translation edge, still distinct from the target's
    decision to rely on the imported negative artifact. -/
def negativeTranslationBridge
    {Source : Type u} {Target : Type v}
    {bridge : Span.{u, v, w} Source Target}
    {SourceNegative : Source → Type p}
    {ImportedNegative : Target → Type q}
    (translate : TranslateAlong bridge SourceNegative ImportedNegative) :
    PJ.IndexedJudgmentBridge where
  SourceIndex := Source
  TargetIndex := Target
  SourceJudgment := SourceNegative
  TargetJudgment := ImportedNegative
  Receipt := RouteReceipt bridge
  carry := by
    intro source target receipt negative
    exact receipt.target_eq ▸
      translate receipt.crossing (receipt.source_eq.symm ▸ negative)

/-- One native negative target-local reliance edge. -/
def negativeRelianceBridge
    {Target : Type v}
    {ImportedNegative : Target → Type q}
    {TargetNegative : Target → Type r}
    (rely : RelyLocally ImportedNegative TargetNegative) :
    PJ.IndexedJudgmentBridge where
  SourceIndex := Target
  TargetIndex := Target
  SourceJudgment := ImportedNegative
  TargetJudgment := TargetNegative
  Receipt importedTarget localTarget := importedTarget = localTarget
  carry := by
    intro importedTarget localTarget sameTarget imported
    exact sameTarget ▸ rely importedTarget imported

/-- A certificate-dependent GT lift supplies one exact PJ entitlement for the
    native positive translation edge.  The target index is determined by the
    retained crossing witness rather than guessed from endpoint equality. -/
def positiveEntitlementOfCertificateLift
    {Source : Type u} {Target : Type v}
    {bridge : Span.{u, v, w} Source Target}
    {SourcePositive : Source → Type p}
    {ImportedPositive : Target → Type q}
    (lift : CertificateLift bridge SourcePositive)
    (translate : TranslateAlong bridge SourcePositive ImportedPositive)
    (source : Source) (positive : SourcePositive source) :
    Σ target : Target,
      (positiveTranslationBridge translate).EntitledFrom source target := by
  obtain ⟨crossing, source_eq⟩ := lift source positive
  exact ⟨bridge.target crossing,
    { sourceEvidence := positive
      receipt :=
        { crossing := crossing
          source_eq := source_eq
          target_eq := rfl } }⟩

/-- Translation evidence becomes input to a *second* entitlement only after
    the target-local reliance bridge and its own exact receipt are supplied. -/
def positiveLocalEntitlementOfTranslated
    {Target : Type v}
    {ImportedPositive : Target → Type q}
    {TargetPositive : Target → Type r}
    (rely : RelyLocally ImportedPositive TargetPositive)
    (target : Target) (imported : ImportedPositive target) :
    (positiveRelianceBridge rely).EntitledFrom target target :=
  { sourceEvidence := imported
    receipt := rfl }

/-- The negative path has the same two-edge shape without identifying its
    evidence families with the positive ones. -/
def negativeLocalEntitlementOfTranslated
    {Target : Type v}
    {ImportedNegative : Target → Type q}
    {TargetNegative : Target → Type r}
    (rely : RelyLocally ImportedNegative TargetNegative)
    (target : Target) (imported : ImportedNegative target) :
    (negativeRelianceBridge rely).EntitledFrom target target :=
  { sourceEvidence := imported
    receipt := rfl }

/-! ## Exact hostile models retained through the PJ interface -/

namespace MissingPositiveLiftAdapter

open LeanProofs.GovernedTransport.Hostile.MissingPositiveLift

/-- The native translation law is vacuous because this hostile span has no
    crossing witness.  Supplying the function does not manufacture a route
    receipt. -/
def translate : TranslateAlong crossing SourcePositive TargetPositive :=
  fun witness => nomatch witness

def pjBridge : PJ.IndexedJudgmentBridge :=
  positiveTranslationBridge translate

/-- The exact native hostile remains visible, and its inhabited source is not
    entitled to either Bool target through the PJ adapter. -/
theorem native_missing_lift_remains_not_entitled :
    (Nonempty (Realized Unit SourcePositive) ∧
      ¬ Nonempty (CertificateLift crossing SourcePositive) ∧
      ¬ Nonempty (Realized Bool TargetPositive)) ∧
    pjBridge.NotEntitledFrom () false ∧
    pjBridge.NotEntitledFrom () true := by
  refine ⟨source_witness_without_lift_does_not_transport, ?_, ?_⟩
  · intro entitled
    exact nomatch entitled.receipt.crossing
  · intro entitled
    exact nomatch entitled.receipt.crossing

end MissingPositiveLiftAdapter

namespace TargetLocalNegativeAdapter

open LeanProofs.GovernedTransport.Hostile

/-- An imported-negative translation can be defined from the empty source
    family only vacuously. -/
def translate : TranslateAlong UnitBool.crossing
    TargetLocalRegression.EmptySourceNegative
    TargetLocalRegression.ImportedNegative :=
  fun _ sourceNegative => nomatch sourceNegative

def pjBridge : PJ.IndexedJudgmentBridge :=
  negativeTranslationBridge translate

/-- Complete target-local evidence still cannot supply source-relative
    negative entitlement.  This carries the exact GT regression packet and
    its source-provenance failure through `NotEntitledFrom`. -/
theorem target_local_evidence_remains_not_entitled :
    (Nonempty (GlobalBlocked Bool
        TargetLocalRegression.TargetLocalNegative) ∧
      ¬ Nonempty (TransportedBlockage UnitBool.crossing
        TargetLocalRegression.EmptySourceNegative
        TargetLocalRegression.ImportedNegative
        TargetLocalRegression.TargetLocalNegative)) ∧
    pjBridge.NotEntitledFrom () false := by
  refine ⟨TargetLocalRegression.target_local_block_cannot_masquerade_as_transport,
    ?_⟩
  intro entitled
  exact nomatch entitled.sourceEvidence

end TargetLocalNegativeAdapter

#print axioms positiveTranslationBridge
#print axioms positiveRelianceBridge
#print axioms negativeTranslationBridge
#print axioms negativeRelianceBridge
#print axioms positiveEntitlementOfCertificateLift
#print axioms positiveLocalEntitlementOfTranslated
#print axioms negativeLocalEntitlementOfTranslated
#print axioms MissingPositiveLiftAdapter.translate
#print axioms MissingPositiveLiftAdapter.pjBridge
#print axioms MissingPositiveLiftAdapter.native_missing_lift_remains_not_entitled
#print axioms TargetLocalNegativeAdapter.translate
#print axioms TargetLocalNegativeAdapter.pjBridge
#print axioms TargetLocalNegativeAdapter.target_local_evidence_remains_not_entitled

end PJ.Instances.GovernedTransport
