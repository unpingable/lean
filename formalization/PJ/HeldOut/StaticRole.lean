/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE
-/

import PJ.Core
import StaticRole.Theorems.ExpansionIndependence
import StaticRole.Theorems.UptakeIndependence

/-!
  Held-out PJ Tranche-A test for the exact ratified StaticRole phase-three
  hierarchy.

  The frozen PJ core is not changed here.  R0--R3 supply exact instances of
  its oriented, index-bound bridge shape.  The richer StaticRole laws about
  coherent reference transport, presentation, failure of factorization,
  same-reduct alternate wiring, and correctness independence remain local
  structure: the PJ core can carry their licensed rung transitions, but does
  not express those laws generically.

  Classification: faithful partial instance requiring a local
  functional-dependence extension.  This is not a defect in the frozen core:
  none of the three primary calculi forced erasure, evaluation, or
  counterfactual output discrimination into PJ-1.
-/

namespace PJ.HeldOut.StaticRole

open _root_.StaticRole
open _root_.StaticRole.Countermodels.DependencyChain
open _root_.StaticRole.Countermodels.RoleHierarchy
open _root_.StaticRole.Countermodels.CoherenceHostiles
open _root_.StaticRole.Countermodels.UptakeHostiles

universe uU

/-- The exact pair of centers indexing one StaticRole rung. -/
abbrev CenterPair (B : StaticBase) := B.Center × B.Center

/-- Endpoint equality for a rung projection.  It carries no target judgment. -/
structure SameCenters {B : StaticBase}
    (source target : CenterPair B) : Prop where
  exact : source = target

/-! ## Downward hierarchy projections

These bridges are the exact local implications R1 → R0, R2 → R1, and
R3 → R2.  Their receipts bind only the identical center pair; the target
judgment is derived by the ratified source definitions/theorem.
-/

def r1ToR0ProjectionBridge
    {B : StaticBase} {I : InformationLayer B}
    (R : RepresentationLayer I) : IndexedJudgmentBridge where
  SourceIndex := CenterPair B
  TargetIndex := CenterPair B
  SourceJudgment := fun index =>
    InternalRoleEncoding R index.1 index.2
  TargetJudgment := fun index =>
    ExternalRoleShift B index.1 index.2
  Receipt := SameCenters
  carry := by
    intro source target receipt r1
    cases receipt.exact
    exact r1.1

def r2ToR1ProjectionBridge
    {B : StaticBase} {I : InformationLayer B}
    {R : RepresentationLayer I}
    (F : SelfReferenceFrame R)
    (A : CoherentReferenceAction F) : IndexedJudgmentBridge where
  SourceIndex := CenterPair B
  TargetIndex := CenterPair B
  SourceJudgment := fun index =>
    ProspectiveDeSeEncoding F A index.1 index.2
  TargetJudgment := fun index =>
    InternalRoleEncoding R index.1 index.2
  Receipt := SameCenters
  carry := by
    intro source target receipt r2
    cases receipt.exact
    exact r2.1

def r3ToR2ProjectionBridge
    {B : StaticBase} {I : InformationLayer B}
    {R : RepresentationLayer I}
    (F : SelfReferenceFrame R)
    (A : CoherentReferenceAction F)
    (U : UptakeLayer.{uU} F A) : IndexedJudgmentBridge where
  SourceIndex := CenterPair B
  TargetIndex := CenterPair B
  SourceJudgment := fun index =>
    FunctionalUptake F A U index.1 index.2
  TargetJudgment := fun index =>
    ProspectiveDeSeEncoding F A index.1 index.2
  Receipt := SameCenters
  carry := by
    intro source target receipt r3
    cases receipt.exact
    exact functional_uptake_implies_r2 r3

/-! ## Exact additional evidence for the upward rung bridges -/

/-- R0 becomes R1 only with the four exact internally hosted role cells.
    The receipt does not store the R0 conjunct or the completed R1 judgment. -/
structure R0ToR1Receipt
    {B : StaticBase} {I : InformationLayer B}
    (R : RepresentationLayer I)
    (source target : CenterPair B) : Prop where
  sameCenters : source = target
  currentAtSource :
    Encodes R target.1 target.1 target.1 .current
  prospectiveAtSource :
    Encodes R target.1 target.1 target.2 .future
  retrospectiveAtTarget :
    Encodes R target.1 target.2 target.1 .past
  currentAtTarget :
    Encodes R target.1 target.2 target.2 .current

def r0ToR1Bridge
    {B : StaticBase} {I : InformationLayer B}
    (R : RepresentationLayer I) : IndexedJudgmentBridge where
  SourceIndex := CenterPair B
  TargetIndex := CenterPair B
  SourceJudgment := fun index =>
    ExternalRoleShift B index.1 index.2
  TargetJudgment := fun index =>
    InternalRoleEncoding R index.1 index.2
  Receipt := R0ToR1Receipt R
  carry := by
    intro source target receipt r0
    cases receipt.sameCenters
    exact ⟨r0, receipt.currentAtSource, receipt.prospectiveAtSource,
      receipt.retrospectiveAtTarget, receipt.currentAtTarget⟩

/-- R1 becomes R2 only with continuation, coherent current-reference
    preservation, and exact forecast hosting/grounding.  No completed R2
    proposition is stored in this receipt. -/
structure R1ToR2Receipt
    {B : StaticBase} {I : InformationLayer B}
    {R : RepresentationLayer I}
    (F : SelfReferenceFrame R)
    (A : CoherentReferenceAction F)
    (source target : CenterPair B) where
  sameCenters : source = target
  continuation : R.continuationCandidate target.1 target.2
  preservation : PreservesCurrentReference F A target.1 target.2
  forecast : I.ForecastToken
  hosted : ForecastHostedFor I forecast target.1 target.2
  grounded :
    R.groundedByForecast
      (F.referenceNode target.1 target.2
        (A.carry target.1 target.2
          (F.currentReference target.1)))
      forecast

def r1ToR2Bridge
    {B : StaticBase} {I : InformationLayer B}
    {R : RepresentationLayer I}
    (F : SelfReferenceFrame R)
    (A : CoherentReferenceAction F) : IndexedJudgmentBridge where
  SourceIndex := CenterPair B
  TargetIndex := CenterPair B
  SourceJudgment := fun index =>
    InternalRoleEncoding R index.1 index.2
  TargetJudgment := fun index =>
    ProspectiveDeSeEncoding F A index.1 index.2
  Receipt := R1ToR2Receipt F A
  carry := by
    intro source target receipt r1
    cases receipt.sameCenters
    exact ⟨r1, receipt.continuation, receipt.preservation,
      receipt.forecast, receipt.hosted, receipt.grounded⟩

/-- R2 becomes R3 only with two exact lawful same-erasure inputs, faithful
    presentation, and observed output discrimination at the same center pair.
    These are concrete witnesses, not a stored use/dependence Boolean. -/
structure R2ToR3Receipt
    {B : StaticBase} {I : InformationLayer B}
    {R : RepresentationLayer I}
    (F : SelfReferenceFrame R)
    (A : CoherentReferenceAction F)
    (U : UptakeLayer.{uU} F A)
    (source target : CenterPair B) where
  sameCenters : source = target
  actual : ProspectiveFunctionalInput F target.1 target.2
  alternate : ProspectiveFunctionalInput F target.1 target.2
  actualLawful : LawfulProspectiveInput F target.1 target.2 actual
  alternateLawful : LawfulProspectiveInput F target.1 target.2 alternate
  actualReference :
    actual.reference =
      A.carry target.1 target.2 (F.currentReference target.1)
  sameErasure : actual.eraseDeSe = alternate.eraseDeSe
  referencesDiffer : actual.reference ≠ alternate.reference
  actualPresented : U.present target.1 target.2 actual = some actual
  alternatePresented :
    U.present target.1 target.2 alternate = some alternate
  outputsDiffer :
    U.evaluate target.1 target.2 actual ≠
      U.evaluate target.1 target.2 alternate

def r2ToR3Bridge
    {B : StaticBase} {I : InformationLayer B}
    {R : RepresentationLayer I}
    (F : SelfReferenceFrame R)
    (A : CoherentReferenceAction F)
    (U : UptakeLayer.{uU} F A) : IndexedJudgmentBridge where
  SourceIndex := CenterPair B
  TargetIndex := CenterPair B
  SourceJudgment := fun index =>
    ProspectiveDeSeEncoding F A index.1 index.2
  TargetJudgment := fun index =>
    FunctionalUptake F A U index.1 index.2
  Receipt := R2ToR3Receipt F A U
  carry := by
    intro source target receipt r2
    cases receipt.sameCenters
    exact ⟨r2, receipt.actual, receipt.alternate,
      receipt.actualLawful, receipt.alternateLawful,
      receipt.actualReference, receipt.sameErasure,
      receipt.referencesDiffer, receipt.actualPresented,
      receipt.alternatePresented, receipt.outputsDiffer⟩

/-! ## Inhabited exact contact -/

def coherenceR0ToR1Entitlement :
    (r0ToR1Bridge coherenceRepresentation).EntitledFrom
      (false, true) (false, true) where
  sourceEvidence := coherence_external_role_shift
  receipt := {
    sameCenters := rfl
    currentAtSource := coherence_representation_has_r1.2.1
    prospectiveAtSource := coherence_representation_has_r1.2.2.1
    retrospectiveAtTarget := coherence_representation_has_r1.2.2.2.1
    currentAtTarget := coherence_representation_has_r1.2.2.2.2
  }

def coherenceR1ToR2Entitlement :
    (r1ToR2Bridge coherenceFrame parityAction).EntitledFrom
      (false, true) (false, true) where
  sourceEvidence := coherence_representation_has_r1
  receipt := {
    sameCenters := rfl
    continuation := .candidate
    preservation := rfl
    forecast := PUnit.unit
    hosted := ⟨rfl, rfl⟩
    grounded := .target true
  }

def coherenceR2ToR3Entitlement :
    (r2ToR3Bridge coherenceFrame parityAction faithfulUptake).EntitledFrom
      (false, true) (false, true) where
  sourceEvidence := coherenceAvailable.toR2
  receipt := {
    sameCenters := rfl
    actual := actualInput
    alternate := alternateInput
    actualLawful := actual_input_lawful
    alternateLawful := alternate_input_lawful
    actualReference := rfl
    sameErasure := rfl
    referencesDiffer := by
      intro equality
      cases equality
    actualPresented := rfl
    alternatePresented := rfl
    outputsDiffer := by
      intro equality
      cases equality
  }

theorem exact_entitlements_recover_r1_r2_r3 :
    InternalRoleEncoding coherenceRepresentation false true ∧
    ProspectiveDeSeEncoding coherenceFrame parityAction false true ∧
    FunctionalUptake coherenceFrame parityAction faithfulUptake
      false true := by
  exact ⟨coherenceR0ToR1Entitlement.targetEvidence,
    coherenceR1ToR2Entitlement.targetEvidence,
    coherenceR2ToR3Entitlement.targetEvidence⟩

/-! ## Strict rung boundaries retained as PJ anti-entitlement -/

theorem r0_without_r1_remains_not_entitled :
    ExternalRoleShift orderedBase false true ∧
    (r0ToR1Bridge emptyRepresentation).NotEntitledFrom
      (false, true) (false, true) := by
  refine ⟨r0_without_r1.1, ?_⟩
  intro entitlement
  exact r0_without_r1.2 entitlement.targetEvidence

theorem r1_without_r2_remains_not_entitled :
    InternalRoleEncoding coherenceRepresentation false true ∧
    (r1ToR2Bridge coherenceFrame fixedAction).NotEntitledFrom
      (false, true) (false, true) := by
  refine ⟨coherence_representation_has_r1, ?_⟩
  intro entitlement
  exact fixed_action_has_no_r2 entitlement.targetEvidence

theorem r2_without_r3_remains_not_entitled :
    ProspectiveDeSeEncoding coherenceFrame parityAction false true ∧
    IndexedJudgmentBridge.NotEntitledFrom
      (r2ToR3Bridge coherenceFrame parityAction neutralizingUptake)
      (false, true) (false, true) := by
  refine ⟨coherenceAvailable.toR2, ?_⟩
  intro entitlement
  exact neutralizing_uptake_has_no_r3 entitlement.targetEvidence

/-! ## StaticRole-local structure deliberately not promoted to PJ.Core -/

/-- R2's route is a lawful coherent reference action and recovers the native
    node-level witness.  PJ carries this as exact receipt evidence but adds no
    generic reference-action law. -/
theorem lawful_reference_transport_boundary :
    PreservesCurrentReference coherenceFrame parityAction false true ∧
    Nonempty (CoherentProspectiveWitness
      coherenceFrame parityAction false true) := by
  exact ⟨rfl, parity_action_has_coherent_witness⟩

/-- Same R2 reduct and evaluator, alternate lawful presentation wiring, and
    opposite R3 results are all retained exactly. -/
theorem same_reduct_presentation_boundary :
    (FunctionalUptake coherenceFrame parityAction faithfulUptake false true ∧
      ¬ FunctionalUptake coherenceFrame parityAction neutralizingUptake
        false true) ∧
    (faithfulUptake.Output = neutralizingUptake.Output ∧
      ∀ c d input,
        faithfulUptake.evaluate c d input =
          neutralizingUptake.evaluate c d input) := by
  exact ⟨same_r2_and_evaluator_presentations_disagree_on_r3,
    central_presentations_share_output_and_evaluator⟩

/-- Failure of factorization through exact de-se erasure distinguishes the
    faithful R3 fixture from the lawful neutralizing presentation. -/
theorem factorization_boundary :
    ¬ FactorsThroughDeSeErasure faithfulUptake false true ∧
    FactorsThroughDeSeErasure neutralizingUptake false true := by
  exact ⟨functional_uptake_not_factors_through_erasure
      faithful_uptake_has_r3,
    neutralizing_uptake_factors_through_erasure⟩

/-- Functional dependence and output correctness remain independent. -/
theorem correctness_boundary :
    (FunctionalUptake coherenceFrame parityAction faithfulUptake false true ∧
      ¬ OutputCorrect true) ∧
    (OutputCorrect false ∧
      ¬ FunctionalUptake coherenceFrame parityAction constantUptake
        false true) := by
  exact ⟨⟨de_se_dependence_without_success.1,
      de_se_dependence_without_success.2.2⟩,
    ⟨successful_output_without_uptake.2.1,
      successful_output_without_uptake.2.2⟩⟩

/-- Presentation availability and forecast consumption do not collapse into
    de-se-dependent uptake. -/
theorem availability_and_consumption_boundaries :
    (neutralizingUptake.PresentedInputAvailable false true actualInput ∧
      ¬ neutralizingUptake.FaithfullyConsumes false true actualInput) ∧
    (forecastOnlyUptake.FaithfullyConsumes false true actualInput ∧
      FactorsThroughDeSeErasure forecastOnlyUptake false true ∧
      ¬ FunctionalUptake coherenceFrame parityAction forecastOnlyUptake
        false true) := by
  exact ⟨⟨presented_availability_without_faithful_consumption.1,
      presented_availability_without_faithful_consumption.2.1⟩,
    faithful_forecast_consumption_still_not_de_se_uptake⟩

/-!
  Held-out verdict: the R0--R3 ladder is a faithful exact instance of the
  minimal indexed-judgment/receipt bridge *at each oriented rung*.  StaticRole
  as a whole is only a faithful partial instance of PJ: its de-se erasure,
  evaluator, factorization, alternate lawful wiring, and correctness laws are
  an irreducible local functional-dependence extension.  Expressing those
  laws generically would require changing the frozen core, so this file does
  not do so.
-/

#print axioms r1ToR0ProjectionBridge
#print axioms r2ToR1ProjectionBridge
#print axioms r3ToR2ProjectionBridge
#print axioms r0ToR1Bridge
#print axioms r1ToR2Bridge
#print axioms r2ToR3Bridge
#print axioms exact_entitlements_recover_r1_r2_r3
#print axioms r0_without_r1_remains_not_entitled
#print axioms r1_without_r2_remains_not_entitled
#print axioms r2_without_r3_remains_not_entitled
#print axioms lawful_reference_transport_boundary
#print axioms same_reduct_presentation_boundary
#print axioms factorization_boundary
#print axioms correctness_boundary
#print axioms availability_and_consumption_boundaries

end PJ.HeldOut.StaticRole
