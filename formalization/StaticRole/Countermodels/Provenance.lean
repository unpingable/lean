/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE
-/

import StaticRole.Countermodels.RoleHierarchy

namespace StaticRole.Countermodels.Provenance

open DependencyChain RoleHierarchy

/-- The provenance fixture varies only this parameter.  All carrier,
    record-coordinate, forecast, and representation data are otherwise fixed. -/
def provenanceInformation (valid : Prop) :
    InformationLayer.{0, 0, 0, 0, 0, 0} orderedBase where
  Stage := Bool
  actualStage := fun center => center
  stageAt := fun stage => stage
  stageAt_actual := fun _ => rfl
  RecordToken := PUnit
  recordAt := fun _ => false
  recordSource := fun _ => false
  recordAbout := fun _ => true
  traceValid := fun _ => valid
  ForecastToken := PUnit
  forecastAt := fun _ => false
  forecastTarget := fun _ => true

def provenanceRecordGrounding
    (node : AtlasNode) (_record : PUnit.{1}) : Prop :=
  node = .dc

/-- One representation definition, parameterized only because its fixed
    information-layer argument is dependent.  Its field bodies do not inspect
    `valid`. -/
def provenanceLayer (valid : Prop) :
    RepresentationLayer (provenanceInformation valid) where
  RepNode := AtlasNode
  nodeStage := fun _ => false
  perspective := fun node => some (atlasPerspective node)
  target := fun node => some (atlasTarget node)
  encodedRole := atlasRole
  mode := prospectiveMode
  repBefore := fun _ _ => False
  groundedByRecord := provenanceRecordGrounding
  groundedByForecast := atlasForecastGrounding
  continuationCandidate := ContinuationPair

theorem provenance_atlas_has_r1 (valid : Prop) :
    InternalRoleEncoding (provenanceLayer valid) false true := by
  exact ⟨ordered_external_role_shift,
    ⟨.cc, rfl, rfl, rfl, rfl⟩,
    ⟨.cd, rfl, rfl, rfl, rfl⟩,
    ⟨.dc, rfl, rfl, rfl, rfl⟩,
    ⟨.dd, rfl, rfl, rfl, rfl⟩⟩

/-- Fixture 9's provenance disagreement on the same inhabited record token. -/
theorem trace_validity_differs :
    (provenanceInformation True).traceValid PUnit.unit ∧
    ¬ (provenanceInformation False).traceValid PUnit.unit := by
  exact ⟨True.intro, fun invalid => invalid⟩

/-- All representation-valued node fields are pointwise identical. -/
theorem provenance_node_fields_agree (node : AtlasNode) :
    (provenanceLayer True).nodeStage node =
        (provenanceLayer False).nodeStage node ∧
    (provenanceLayer True).perspective node =
        (provenanceLayer False).perspective node ∧
    (provenanceLayer True).target node =
        (provenanceLayer False).target node ∧
    (provenanceLayer True).encodedRole node =
        (provenanceLayer False).encodedRole node ∧
    (provenanceLayer True).mode node =
        (provenanceLayer False).mode node := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- All representation relations, including both grounding links, agree
    pointwise.  Iffs avoid proposition extensionality. -/
theorem provenance_node_relations_agree
    (first second : AtlasNode) (record forecast : PUnit) :
    ((provenanceLayer True).repBefore first second ↔
      (provenanceLayer False).repBefore first second) ∧
    ((provenanceLayer True).groundedByRecord first record ↔
      (provenanceLayer False).groundedByRecord first record) ∧
    ((provenanceLayer True).groundedByForecast first forecast ↔
      (provenanceLayer False).groundedByForecast first forecast) := by
  exact ⟨Iff.rfl, Iff.rfl, Iff.rfl⟩

theorem provenance_continuation_agrees (c d : Bool) :
    (provenanceLayer True).continuationCandidate c d ↔
      (provenanceLayer False).continuationCandidate c d := by
  exact Iff.rfl

theorem provenance_r1_invariant :
    InternalRoleEncoding (provenanceLayer True) false true ↔
      InternalRoleEncoding (provenanceLayer False) false true := by
  exact ⟨fun _ => provenance_atlas_has_r1 False,
    fun _ => provenance_atlas_has_r1 True⟩

/-- Option B provenance receipt.  This theorem records only definitional
    nondependence: `traceValid` is outside R1, and the representation fields
    below do not inspect it.  It is deliberately not a substantive invariance
    theorem and makes no repaired R2 claim. -/
theorem trace_validity_definitional_nondependence_for_r1 :
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
  refine ⟨trace_validity_differs.1, trace_validity_differs.2,
    provenance_node_fields_agree, provenance_node_relations_agree,
    provenance_continuation_agrees, provenance_r1_invariant⟩

end StaticRole.Countermodels.Provenance
