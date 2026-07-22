/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE
-/

import StaticRole.Countermodels.DependencyChain

namespace StaticRole.Countermodels.RoleHierarchy

open DependencyChain

/-- Fixture 5's finite current-reference coordinate grid.  Every node carries
    a current role, so the grid can realize a lawful current anchor while it
    cannot realize R1's future cell. -/
def selfOnlyLayer : RepresentationLayer emptyInformation where
  RepNode := Bool × Bool
  nodeStage := Prod.fst
  perspective := fun node => some node.2
  target := fun node => some node.2
  encodedRole := fun _ => .current
  mode := fun _ => .occurrent
  repBefore := fun _ _ => False
  groundedByRecord := fun _ record => nomatch record
  groundedByForecast := fun _ forecast => nomatch forecast
  continuationCandidate := fun _ _ => False

def selfOnlyFrame : SelfReferenceFrame.{0} selfOnlyLayer where
  Reference := PUnit
  referenceNode := fun host represented _ => (host, represented)
  currentReference := fun _ => PUnit.unit
  referenceNode_injective := by
    intro host represented left right _
    cases left
    cases right
    rfl
  nodeStage_reference := by
    intro host represented ref
    rfl
  perspective_reference := by
    intro host represented ref
    rfl
  target_reference := by
    intro host represented ref
    rfl
  role_reference := by
    intro host represented ref
    rfl
  grounding_coordinates := by
    intro host represented ref forecast
    exact nomatch forecast

theorem self_only_current_node :
    CurrentSelfNode selfOnlyFrame false (false, false) := by
  rfl

theorem self_only_does_not_encode_future :
    ¬ Encodes selfOnlyLayer false false true .future := by
  rintro ⟨node, _, _, _, roleEq⟩
  exact CenterRole.noConfusion roleEq

/-- Fixture 5: a valid current self-node supplies neither the cross-center
    future cell nor the rest of R1's atlas. -/
theorem self_location_without_r1 :
    CurrentSelfNode selfOnlyFrame false (false, false) ∧
    ¬ InternalRoleEncoding selfOnlyLayer false true := by
  exact ⟨self_only_current_node, fun h =>
    self_only_does_not_encode_future h.2.2.1⟩

/-- Fixture 6's representation layer has no nodes at all. -/
def emptyRepresentation : RepresentationLayer emptyInformation where
  RepNode := Empty
  nodeStage := fun node => nomatch node
  perspective := fun node => nomatch node
  target := fun node => nomatch node
  encodedRole := fun node => nomatch node
  mode := fun node => nomatch node
  repBefore := fun node => nomatch node
  groundedByRecord := fun node => nomatch node
  groundedByForecast := fun node => nomatch node
  continuationCandidate := fun _ _ => False

theorem empty_representation_does_not_encode_current :
    ¬ Encodes emptyRepresentation false false false .current := by
  rintro ⟨node, _⟩
  exact nomatch node

/-- Fixture 6: the physical base realizes R0 while its empty representation
    expansion cannot realize R1. -/
theorem r0_without_r1 :
    ExternalRoleShift orderedBase false true ∧
    ¬ InternalRoleEncoding emptyRepresentation false true := by
  exact ⟨ordered_external_role_shift, fun h =>
    empty_representation_does_not_encode_current h.2.1⟩

/-- Four explicit nodes for the cross-center atlas. -/
inductive AtlasNode
  | cc
  | cd
  | dc
  | dd
  deriving DecidableEq, Repr

def atlasPerspective : AtlasNode → Bool
  | .cc | .cd => false
  | .dc | .dd => true

def atlasTarget : AtlasNode → Bool
  | .cc | .dc => false
  | .cd | .dd => true

def atlasRole : AtlasNode → CenterRole
  | .cc | .dd => .current
  | .cd => .future
  | .dc => .past

def prospectiveMode : AtlasNode → EpistemicMode
  | .cc => .occurrent
  | .cd => .neutral
  | .dc => .neutral
  | .dd => .anticipatory

/-- Abstract observer-model data, deliberately distinct from the physical
    `BoolBefore` causal relation even though this finite fixture exhibits the
    same ordered pair. -/
inductive ContinuationPair : Bool → Bool → Prop
  | candidate : ContinuationPair false true

/-- Fixture 7: a complete role atlas with neutral modes and none of R2's
    additional representation or information commitments. -/
def neutralAtlasLayer : RepresentationLayer emptyInformation where
  RepNode := AtlasNode
  nodeStage := fun _ => false
  perspective := fun node => some (atlasPerspective node)
  target := fun node => some (atlasTarget node)
  encodedRole := atlasRole
  mode := fun _ => .neutral
  repBefore := fun _ _ => False
  groundedByRecord := fun _ record => nomatch record
  groundedByForecast := fun _ forecast => nomatch forecast
  continuationCandidate := fun _ _ => False

theorem neutral_atlas_encodes_cc :
    Encodes neutralAtlasLayer false false false .current := by
  exact ⟨.cc, rfl, rfl, rfl, rfl⟩

theorem neutral_atlas_encodes_cd :
    Encodes neutralAtlasLayer false false true .future := by
  exact ⟨.cd, rfl, rfl, rfl, rfl⟩

theorem neutral_atlas_encodes_dc :
    Encodes neutralAtlasLayer false true false .past := by
  exact ⟨.dc, rfl, rfl, rfl, rfl⟩

theorem neutral_atlas_encodes_dd :
    Encodes neutralAtlasLayer false true true .current := by
  exact ⟨.dd, rfl, rfl, rfl, rfl⟩

theorem neutral_atlas_has_r1 :
    InternalRoleEncoding neutralAtlasLayer false true := by
  exact ⟨ordered_external_role_shift,
    neutral_atlas_encodes_cc, neutral_atlas_encodes_cd,
    neutral_atlas_encodes_dc, neutral_atlas_encodes_dd⟩

theorem neutral_atlas_modes :
    ∀ node, neutralAtlasLayer.mode node = .neutral := by
  intro node
  rfl

theorem neutral_atlas_has_no_forecast :
    ∀ _forecast : emptyInformation.ForecastToken, False := by
  intro forecast
  exact nomatch forecast

theorem neutral_atlas_has_no_continuation :
    ¬ neutralAtlasLayer.continuationCandidate false true := by
  intro continuation
  exact continuation

/-- A phase-one information fixture retained for the R1 and accuracy controls.
    The repaired positive no-record R2 fixture lives in `CoherenceHostiles`. -/
def noRecordForecastInformation :
    InformationLayer.{0, 0, 0, 0, 0, 0} orderedBase where
  Stage := Bool
  actualStage := fun center => center
  stageAt := fun stage => stage
  stageAt_actual := fun _ => rfl
  RecordToken := Empty
  recordAt := fun record => nomatch record
  recordSource := fun record => nomatch record
  recordAbout := fun record => nomatch record
  traceValid := fun record => nomatch record
  ForecastToken := PUnit
  forecastAt := fun _ => false
  forecastTarget := fun _ => true

def atlasForecastGrounding
    (node : AtlasNode) (_forecast : PUnit.{1}) : Prop :=
  node = .dd

/-- A four-cell atlas with display-oriented modes and forecast grounding.
    This layer alone makes no repaired R2 claim: it supplies no reference frame
    or coherent carry action. -/
def prospectiveAtlasLayer : RepresentationLayer noRecordForecastInformation where
  RepNode := AtlasNode
  nodeStage := fun _ => false
  perspective := fun node => some (atlasPerspective node)
  target := fun node => some (atlasTarget node)
  encodedRole := atlasRole
  mode := prospectiveMode
  repBefore := fun _ _ => False
  groundedByRecord := fun _ record => nomatch record
  groundedByForecast := atlasForecastGrounding
  continuationCandidate := ContinuationPair

theorem prospective_atlas_has_r1 :
    InternalRoleEncoding prospectiveAtlasLayer false true := by
  exact ⟨ordered_external_role_shift,
    ⟨.cc, rfl, rfl, rfl, rfl⟩,
    ⟨.cd, rfl, rfl, rfl, rfl⟩,
    ⟨.dc, rfl, rfl, rfl, rfl⟩,
    ⟨.dd, rfl, rfl, rfl, rfl⟩⟩

theorem prospective_atlas_has_no_records :
    ∀ _record : noRecordForecastInformation.RecordToken, False := by
  intro record
  exact nomatch record

/-- A metadata-only variant of `prospectiveAtlasLayer`.  It is retained to
    demonstrate that R1 ignores epistemic mode, not as an R2 separation. -/
def neutralForecastAtlasLayer :
    RepresentationLayer noRecordForecastInformation where
  RepNode := AtlasNode
  nodeStage := fun _ => false
  perspective := fun node => some (atlasPerspective node)
  target := fun node => some (atlasTarget node)
  encodedRole := atlasRole
  mode := fun _ => .neutral
  repBefore := fun _ _ => False
  groundedByRecord := fun _ record => nomatch record
  groundedByForecast := atlasForecastGrounding
  continuationCandidate := ContinuationPair

theorem neutral_forecast_atlas_has_r1 :
    InternalRoleEncoding neutralForecastAtlasLayer false true := by
  exact ⟨ordered_external_role_shift,
    ⟨.cc, rfl, rfl, rfl, rfl⟩,
    ⟨.cd, rfl, rfl, rfl, rfl⟩,
    ⟨.dc, rfl, rfl, rfl, rfl⟩,
    ⟨.dd, rfl, rfl, rfl, rfl⟩⟩

/-- The R1-negative half of the same-information R1 pair retains all four
    nodes and represented coordinates, but deliberately misencodes every cell
    as current. -/
def misroleAtlasLayer : RepresentationLayer noRecordForecastInformation where
  RepNode := AtlasNode
  nodeStage := fun _ => false
  perspective := fun node => some (atlasPerspective node)
  target := fun node => some (atlasTarget node)
  encodedRole := fun _ => .current
  mode := fun _ => .neutral
  repBefore := fun _ _ => False
  groundedByRecord := fun _ record => nomatch record
  groundedByForecast := atlasForecastGrounding
  continuationCandidate := ContinuationPair

theorem misrole_atlas_does_not_encode_future :
    ¬ Encodes misroleAtlasLayer false false true .future := by
  rintro ⟨node, _, _, _, roleEq⟩
  cases node <;> exact CenterRole.noConfusion roleEq

theorem misrole_atlas_has_no_r1 :
    ¬ InternalRoleEncoding misroleAtlasLayer false true := by
  intro r1
  exact misrole_atlas_does_not_encode_future r1.2.2.1

/-- The positive layer's future cell incurs a genuine external-role
    obligation. -/
theorem prospective_cd_is_accurate :
    AccurateEncoding prospectiveAtlasLayer .cd := by
  exact ⟨false, true, rfl, rfl, ordered_center_before⟩

/-- Merely having the right represented coordinates does not make a
    mislabelled node accurate. -/
theorem misrole_cd_is_not_accurate :
    ¬ AccurateEncoding misroleAtlasLayer .cd := by
  rintro ⟨evaluation, representedTarget, perspectiveEq, targetEq, hext⟩
  have evaluationEq : evaluation = false :=
    (Option.some.inj perspectiveEq).symm
  have representedTargetEq : representedTarget = true :=
    (Option.some.inj targetEq).symm
  rw [evaluationEq, representedTargetEq] at hext
  change false = true at hext
  cases hext

/-- The central pair agrees on every field used by R1. -/
theorem central_atlas_content_agrees (node : AtlasNode) :
    neutralForecastAtlasLayer.nodeStage node =
        prospectiveAtlasLayer.nodeStage node ∧
    neutralForecastAtlasLayer.perspective node =
        prospectiveAtlasLayer.perspective node ∧
    neutralForecastAtlasLayer.target node =
        prospectiveAtlasLayer.target node ∧
    neutralForecastAtlasLayer.encodedRole node =
        prospectiveAtlasLayer.encodedRole node := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem central_atlas_relations_agree
    (first second : AtlasNode) (forecast : PUnit) :
    (neutralForecastAtlasLayer.repBefore first second ↔
      prospectiveAtlasLayer.repBefore first second) ∧
    (neutralForecastAtlasLayer.groundedByForecast first forecast ↔
      prospectiveAtlasLayer.groundedByForecast first forecast) := by
  exact ⟨Iff.rfl, Iff.rfl⟩

theorem central_continuation_agrees (c d : Bool) :
    neutralForecastAtlasLayer.continuationCandidate c d ↔
      prospectiveAtlasLayer.continuationCandidate c d := by
  exact Iff.rfl

end StaticRole.Countermodels.RoleHierarchy
