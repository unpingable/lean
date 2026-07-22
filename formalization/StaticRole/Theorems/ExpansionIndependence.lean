/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE
-/

import StaticRole.Countermodels.Provenance
import StaticRole.Countermodels.CoherenceHostiles

namespace StaticRole.Theorems.ExpansionIndependence

open Countermodels.DependencyChain
open Countermodels.RoleHierarchy
open Countermodels.Provenance
open Countermodels.CoherenceHostiles

/-- Required separation: R0 does not force an internal role atlas. -/
theorem exists_r0_not_r1 :
    ∃ R : RepresentationLayer.{0, 0, 0, 0, 0, 0, 0} emptyInformation,
      ExternalRoleShift orderedBase false true ∧
      ¬ InternalRoleEncoding R false true := by
  exact ⟨emptyRepresentation, r0_without_r1⟩

/-- One literal physical-information reduct admits an R1 expansion and a
    same-carrier, same-coordinate expansion that mislabels its role cells. -/
theorem same_information_reduct_different_r1 :
    InternalRoleEncoding prospectiveAtlasLayer false true ∧
    ¬ InternalRoleEncoding misroleAtlasLayer false true := by
  exact ⟨prospective_atlas_has_r1, misrole_atlas_has_no_r1⟩

/-- The R1 disagreement is not caused by node or represented-coordinate
    absence: those fields agree pointwise. -/
theorem same_information_r1_coordinates_agree (node : AtlasNode) :
    prospectiveAtlasLayer.nodeStage node =
        misroleAtlasLayer.nodeStage node ∧
    prospectiveAtlasLayer.perspective node =
        misroleAtlasLayer.perspective node ∧
    prospectiveAtlasLayer.target node =
        misroleAtlasLayer.target node := by
  exact ⟨rfl, rfl, rfl⟩

/-- Accuracy remains a separate adequacy obligation: the proper future cell
    is accurate and the same-coordinate, current-labelled cell is not. -/
theorem same_information_r1_accuracy_separates :
    AccurateEncoding prospectiveAtlasLayer .cd ∧
    ¬ AccurateEncoding misroleAtlasLayer .cd := by
  exact ⟨prospective_cd_is_accurate, misrole_cd_is_not_accurate⟩

/-- Repaired R1/R2 separation.  The negative expansion has a lawful total
    action, continuation, forecast, grounding, and the complete R1 atlas; its
    action fails only to carry the shared current-reference section. -/
theorem exists_r1_not_r2 :
    ∃ (R : RepresentationLayer.{0, 0, 0, 0, 0, 0, 0}
        coherenceInformation)
      (F : SelfReferenceFrame.{0} R)
      (A : CoherentReferenceAction F),
      InternalRoleEncoding R false true ∧
      ¬ ProspectiveDeSeEncoding F A false true := by
  exact ⟨coherenceRepresentation, coherenceFrame, fixedAction,
    coherence_representation_has_r1, fixed_action_has_no_r2⟩

/-- The repaired positive construction uses a forecast but its literal shared
    information reduct has no record-token inhabitant. -/
theorem exists_r2_without_records :
    ∃ (R : RepresentationLayer.{0, 0, 0, 0, 0, 0, 0}
        coherenceInformation)
      (F : SelfReferenceFrame.{0} R)
      (A : CoherentReferenceAction F),
      ProspectiveDeSeEncoding F A false true ∧
      (∀ _record : coherenceInformation.RecordToken, False) := by
  exact ⟨coherenceRepresentation, coherenceFrame, parityAction,
    r2_without_record_tokens⟩

/-- Phase two's critical result: one literal base, information layer,
    representation layer, and reference frame support two globally lawful
    actions which disagree on R2. -/
theorem same_information_reduct_different_r2 :
    ProspectiveDeSeEncoding coherenceFrame parityAction false true ∧
    ¬ ProspectiveDeSeEncoding coherenceFrame fixedAction false true :=
  same_reduct_lawful_actions_disagree_on_r2

/-- The same pair also disagrees on recovery of the rich node-level coherent
    witness, not merely on the surface R2 predicate. -/
theorem same_information_reduct_different_coherent_transport :
    Nonempty (CoherentProspectiveWitness
        coherenceFrame parityAction false true) ∧
    ¬ Nonempty (CoherentProspectiveWitness
        coherenceFrame fixedAction false true) :=
  same_reduct_lawful_actions_disagree_on_coherent_transport

/-- Both explicit expansion values reduce to the same representation and
    frame terms.  Only their `referenceAction` fields differ. -/
theorem same_information_r2_expansion_reduct_is_literal :
    parityExpansion.representation = coherenceRepresentation ∧
    fixedExpansion.representation = coherenceRepresentation ∧
    parityExpansion.referenceFrame = coherenceFrame ∧
    fixedExpansion.referenceFrame = coherenceFrame := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- A metadata-only comparison retained from phase one.  Both layers satisfy
    R1 and agree on every R1-relevant field and relation; this theorem makes no
    claim about the repaired R2 bridge. -/
theorem epistemic_remoding_preserves_r1_fixture :
    InternalRoleEncoding neutralForecastAtlasLayer false true ∧
    InternalRoleEncoding prospectiveAtlasLayer false true ∧
    (∀ node,
      neutralForecastAtlasLayer.nodeStage node =
          prospectiveAtlasLayer.nodeStage node ∧
      neutralForecastAtlasLayer.perspective node =
          prospectiveAtlasLayer.perspective node ∧
      neutralForecastAtlasLayer.target node =
          prospectiveAtlasLayer.target node ∧
      neutralForecastAtlasLayer.encodedRole node =
          prospectiveAtlasLayer.encodedRole node) ∧
    (∀ first second forecast,
      (neutralForecastAtlasLayer.repBefore first second ↔
        prospectiveAtlasLayer.repBefore first second) ∧
      (neutralForecastAtlasLayer.groundedByForecast first forecast ↔
        prospectiveAtlasLayer.groundedByForecast first forecast)) ∧
    (∀ c d,
      neutralForecastAtlasLayer.continuationCandidate c d ↔
        prospectiveAtlasLayer.continuationCandidate c d) := by
  refine ⟨neutral_forecast_atlas_has_r1, prospective_atlas_has_r1,
    central_atlas_content_agrees, ?_, central_continuation_agrees⟩
  intro first second forecast
  exact central_atlas_relations_agree first second forecast

/-- Option B provenance boundary: this is a definitional nondependence receipt
    for R1 only, not a substantive representation-invariance theorem. -/
theorem r1_trace_validity_definitional_nondependence :
    (provenanceInformation True).traceValid PUnit.unit ∧
    ¬ (provenanceInformation False).traceValid PUnit.unit ∧
    (∀ node,
      (provenanceLayer True).nodeStage node =
          (provenanceLayer False).nodeStage node ∧
      (provenanceLayer True).perspective node =
          (provenanceLayer False).perspective node ∧
      (provenanceLayer True).target node =
          (provenanceLayer False).target node ∧
      (provenanceLayer True).encodedRole node =
          (provenanceLayer False).encodedRole node ∧
      (provenanceLayer True).mode node =
          (provenanceLayer False).mode node) ∧
    (∀ first second record forecast,
      ((provenanceLayer True).repBefore first second ↔
        (provenanceLayer False).repBefore first second) ∧
      ((provenanceLayer True).groundedByRecord first record ↔
        (provenanceLayer False).groundedByRecord first record) ∧
      ((provenanceLayer True).groundedByForecast first forecast ↔
        (provenanceLayer False).groundedByForecast first forecast)) ∧
    (∀ c d,
      (provenanceLayer True).continuationCandidate c d ↔
        (provenanceLayer False).continuationCandidate c d) ∧
    (InternalRoleEncoding (provenanceLayer True) false true ↔
      InternalRoleEncoding (provenanceLayer False) false true) := by
  exact trace_validity_definitional_nondependence_for_r1

end StaticRole.Theorems.ExpansionIndependence
