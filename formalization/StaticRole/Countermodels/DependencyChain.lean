/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE
-/

import StaticRole.Representation.DeSeProjection

namespace StaticRole.Countermodels.DependencyChain

/-- The sole nontrivial physical edge used by the finite specimens. -/
inductive BoolBefore : Bool → Bool → Prop
  | edge : BoolBefore false true

theorem boolBefore_irrefl : Irreflexive BoolBefore := by
  intro value beforeSelf
  cases beforeSelf

theorem boolBefore_trans : Transitive BoolBefore := by
  intro first middle last firstBeforeMiddle middleBeforeLast
  cases firstBeforeMiddle
  cases middleBeforeLast

/-- Fixture 1: a nontrivial causal order whose center sort is empty. -/
def causalOrderNoCenters : StaticBase.{0, 0, 0} where
  Event := Bool
  Observer := PUnit
  Center := Empty
  causal := BoolBefore
  causal_irrefl := boolBefore_irrefl
  causal_trans := boolBefore_trans
  owner := fun center => nomatch center
  «at» := fun center => nomatch center

theorem causal_order_without_observer_centers :
    causalOrderNoCenters.causal false true ∧
    (∀ _center : causalOrderNoCenters.Center, False) := by
  exact ⟨.edge, fun center => nomatch center⟩

/-- The shared two-center physical base.  There is no global linear-order
    field: `BoolBefore` supplies only the exhibited edge. -/
def orderedBase : StaticBase.{0, 0, 0} where
  Event := Bool
  Observer := PUnit
  Center := Bool
  causal := BoolBefore
  causal_irrefl := boolBefore_irrefl
  causal_trans := boolBefore_trans
  owner := fun _ => PUnit.unit
  «at» := fun center => center

theorem ordered_center_before : CenterBefore orderedBase false true := by
  exact ⟨rfl, .edge⟩

theorem ordered_external_role_shift :
    ExternalRoleShift orderedBase false true := by
  exact ⟨rfl, ordered_center_before, rfl, ordered_center_before,
    ordered_center_before, rfl⟩

/-- Fixture 2's information layer: centers and actual stages, but no records
    (and no forecasts, which are not needed at this dependency rung). -/
def emptyInformation :
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
  ForecastToken := Empty
  forecastAt := fun forecast => nomatch forecast
  forecastTarget := fun forecast => nomatch forecast

theorem centers_and_stages_without_records :
    CenterBefore orderedBase false true ∧
    emptyInformation.stageAt (emptyInformation.actualStage false) = false ∧
    emptyInformation.stageAt (emptyInformation.actualStage true) = true ∧
    (∀ _record : emptyInformation.RecordToken, False) := by
  exact ⟨ordered_center_before, rfl, rfl,
    fun record => nomatch record⟩

/-- Information for fixture 3.  Source and subject are deliberately distinct,
    and mnemonic mode is not inferred from either coordinate. -/
def mnemonicInformation :
    InformationLayer.{0, 0, 0, 0, 0, 0} orderedBase where
  Stage := Bool
  actualStage := fun center => center
  stageAt := fun stage => stage
  stageAt_actual := fun _ => rfl
  RecordToken := PUnit
  recordAt := fun _ => false
  recordSource := fun _ => false
  recordAbout := fun _ => true
  traceValid := fun _ => True
  ForecastToken := Empty
  forecastAt := fun forecast => nomatch forecast
  forecastTarget := fun forecast => nomatch forecast

def mnemonicLayer : RepresentationLayer mnemonicInformation where
  RepNode := PUnit
  nodeStage := fun _ => false
  perspective := fun _ => some false
  target := fun _ => some false
  encodedRole := fun _ => .current
  mode := fun _ => .mnemonic
  repBefore := fun _ _ => False
  groundedByRecord := fun _ _ => True
  groundedByForecast := fun _ forecast => nomatch forecast
  continuationCandidate := fun _ _ => False

/-- Fixture 3: a record-grounded mnemonic node does not create a represented
    ordering between nodes. -/
theorem mnemonic_representation_without_represented_succession :
    MemoryAttributed mnemonicLayer PUnit.unit ∧
    ¬ ∃ first second,
      RepresentsSuccession mnemonicLayer false first second := by
  constructor
  · exact ⟨rfl, ⟨PUnit.unit, True.intro⟩⟩
  · rintro ⟨first, second, _, _, before⟩
    exact before

/-- A representation-only node ordering, deliberately distinct from the
    physical `BoolBefore` causal relation. -/
inductive NodeBefore : Bool → Bool → Prop
  | represented : NodeBefore false true

/-- Two stage-local nodes with an independent representation ordering. -/
def successionLayer : RepresentationLayer emptyInformation where
  RepNode := Bool
  nodeStage := fun _ => false
  perspective := fun node => some node
  target := fun node => some node
  encodedRole := fun _ => .current
  mode := fun _ => .neutral
  repBefore := NodeBefore
  groundedByRecord := fun _ record => nomatch record
  groundedByForecast := fun _ forecast => nomatch forecast
  continuationCandidate := fun _ _ => False

/-- The two-node succession layer cannot realize the total, coordinate-lawful
    reference frame required by the repaired de se signature: at host `true`
    every node is still hosted at stage `false`. -/
theorem succession_layer_has_no_self_reference_frame :
    ¬ Nonempty (SelfReferenceFrame.{0} successionLayer) := by
  rintro ⟨frame⟩
  have atTrue :=
    frame.nodeStage_reference true true (frame.currentReference true)
  change false = true at atTrue
  cases atTrue

/-- Fixture 4, repaired: node-level represented succession is available, but
    no lawful self-reference coordinate frame can be installed on this same
    representation layer. -/
theorem represented_succession_without_self_location :
    RepresentsSuccession successionLayer false false true ∧
    ¬ Nonempty (SelfReferenceFrame.{0} successionLayer) := by
  exact ⟨⟨rfl, rfl, .represented⟩,
    succession_layer_has_no_self_reference_frame⟩

end StaticRole.Countermodels.DependencyChain
