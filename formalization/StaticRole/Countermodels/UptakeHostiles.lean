/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE
-/

import StaticRole.Functional.Dependence
import StaticRole.Countermodels.CoherenceHostiles

namespace StaticRole.Countermodels.UptakeHostiles

open StaticRole.Countermodels.CoherenceHostiles

/-! The phase-two Bool model already supplies two lawful and equally grounded
    target-fiber references.  Phase three varies only how that shared input is
    presented to one shared evaluator. -/

def coherenceAvailable : AvailableProspectiveEncoding
    coherenceFrame parityAction false true where
  roleEncoding := coherence_representation_has_r1
  continuation := .candidate
  preservation := rfl
  forecast := PUnit.unit
  hosted := ⟨rfl, rfl⟩
  grounded := .target true

def actualInput : ProspectiveFunctionalInput coherenceFrame false true where
  reference := true
  forecast := PUnit.unit

def alternateInput : ProspectiveFunctionalInput coherenceFrame false true where
  reference := false
  forecast := PUnit.unit

theorem actual_input_lawful :
    LawfulProspectiveInput coherenceFrame false true actualInput := by
  exact ⟨⟨rfl, rfl⟩, .target true⟩

theorem alternate_input_lawful :
    LawfulProspectiveInput coherenceFrame false true alternateInput := by
  exact ⟨⟨rfl, rfl⟩, .target false⟩

/-- Faithful presentation and a reference-sensitive evaluator. -/
def faithfulUptake : UptakeLayer coherenceFrame parityAction where
  Output := Bool
  present := fun _ _ input => some input
  present_erasure := by
    intro c d input supplied presented
    exact congrArg ProspectiveFunctionalInput.eraseDeSe
      (Option.some.inj presented.symm)
  present_lawful := by
    intro c d input supplied lawful presented
    rw [Option.some.inj presented.symm]
    exact lawful
  evaluate := fun _ _ input => input.reference

/-- A lawful presentation which retains the forecast but normalizes either
    target-fiber coordinate to the independently valid `false` reference. -/
def neutralizingUptake : UptakeLayer coherenceFrame parityAction where
  Output := Bool
  present := fun _ _ input => some {
    reference := false
    forecast := input.forecast
  }
  present_erasure := by
    intro c d input supplied presented
    have suppliedEq := Option.some.inj presented.symm
    cases suppliedEq
    rfl
  present_lawful := by
    intro c d input supplied lawful presented
    have suppliedEq := Option.some.inj presented.symm
    cases suppliedEq
    rcases lawful with ⟨hosted, grounded⟩
    cases grounded
    exact ⟨hosted, .target false⟩
  evaluate := fun _ _ input => input.reference

/-- Availability may be refused before evaluation; no primitive flag records
    that refusal as functional use. -/
def refusingUptake : UptakeLayer coherenceFrame parityAction where
  Output := Bool
  present := fun _ _ _ => none
  present_erasure := by
    intro c d input supplied presented
    cases presented
  present_lawful := by
    intro c d input supplied lawful presented
    cases presented
  evaluate := fun _ _ input => input.reference

/-- A correct-looking result can be constant and wholly input-insensitive. -/
def constantUptake : UptakeLayer coherenceFrame parityAction where
  Output := Bool
  present := fun _ _ input => some input
  present_erasure := by
    intro c d input supplied presented
    exact congrArg ProspectiveFunctionalInput.eraseDeSe
      (Option.some.inj presented.symm)
  present_lawful := by
    intro c d input supplied lawful presented
    rw [Option.some.inj presented.symm]
    exact lawful
  evaluate := fun _ _ _ => false

/-- This evaluator consumes the retained forecast projection, but cannot
    discriminate any erased reference coordinate. -/
def forecastOnlyUptake : UptakeLayer coherenceFrame parityAction where
  Output := PUnit
  present := fun _ _ input => some input
  present_erasure := by
    intro c d input supplied presented
    exact congrArg ProspectiveFunctionalInput.eraseDeSe
      (Option.some.inj presented.symm)
  present_lawful := by
    intro c d input supplied lawful presented
    rw [Option.some.inj presented.symm]
    exact lawful
  evaluate := fun _ _ input => input.forecast

theorem faithful_uptake_has_r3 :
    FunctionalUptake coherenceFrame parityAction faithfulUptake false true := by
  refine ⟨coherenceAvailable.toR2, actualInput, alternateInput,
    actual_input_lawful, alternate_input_lawful, rfl, rfl, ?_, rfl, rfl, ?_⟩
  · intro equal
    cases equal
  · intro equal
    cases equal

theorem neutralizing_uptake_factors_through_erasure :
    FactorsThroughDeSeErasure neutralizingUptake false true := by
  refine ⟨fun _ => some false, ?_⟩
  intro input lawful
  rfl

theorem neutralizing_uptake_has_no_r3 :
    ¬ FunctionalUptake coherenceFrame parityAction neutralizingUptake
      false true := by
  intro uptake
  exact (functional_uptake_not_factors_through_erasure uptake)
    neutralizing_uptake_factors_through_erasure

theorem refusing_uptake_has_no_r3 :
    ¬ FunctionalUptake coherenceFrame parityAction refusingUptake
      false true := by
  rintro ⟨_, actual, alternate, _, _, _, _, _, actualPresented, _⟩
  cases actualPresented

theorem constant_uptake_factors_through_erasure :
    FactorsThroughDeSeErasure constantUptake false true := by
  refine ⟨fun _ => some false, ?_⟩
  intro input lawful
  rfl

theorem constant_uptake_has_no_r3 :
    ¬ FunctionalUptake coherenceFrame parityAction constantUptake false true := by
  intro uptake
  exact (functional_uptake_not_factors_through_erasure uptake)
    constant_uptake_factors_through_erasure

theorem forecast_only_factors_through_erasure :
    FactorsThroughDeSeErasure forecastOnlyUptake false true := by
  refine ⟨fun forecast => some forecast, ?_⟩
  intro input lawful
  rfl

theorem forecast_only_has_no_r3 :
    ¬ FunctionalUptake coherenceFrame parityAction forecastOnlyUptake
      false true := by
  intro uptake
  exact (functional_uptake_not_factors_through_erasure uptake)
    forecast_only_factors_through_erasure

/-- The critical phase-three shared-reduct pair: one literal R2 object and
    evaluator, with only the concrete presentation function changed. -/
theorem same_r2_and_evaluator_presentations_disagree_on_r3 :
    FunctionalUptake coherenceFrame parityAction faithfulUptake false true ∧
    ¬ FunctionalUptake coherenceFrame parityAction neutralizingUptake
      false true := by
  exact ⟨faithful_uptake_has_r3, neutralizing_uptake_has_no_r3⟩

theorem central_presentations_share_output_and_evaluator :
    faithfulUptake.Output = neutralizingUptake.Output ∧
    (∀ c d input,
      faithfulUptake.evaluate c d input =
        neutralizingUptake.evaluate c d input) := by
  exact ⟨rfl, fun _ _ _ => rfl⟩

theorem r2_without_uptake :
    ProspectiveDeSeEncoding coherenceFrame parityAction false true ∧
    ¬ FunctionalUptake coherenceFrame parityAction neutralizingUptake
      false true := by
  exact ⟨coherenceAvailable.toR2, neutralizing_uptake_has_no_r3⟩

theorem availability_without_consumption :
    Nonempty (AvailableProspectiveEncoding coherenceFrame parityAction
      false true) ∧
    refusingUptake.run false true coherenceAvailable.input = none ∧
    ¬ FunctionalUptake coherenceFrame parityAction refusingUptake
      false true := by
  exact ⟨⟨coherenceAvailable⟩, rfl, refusing_uptake_has_no_r3⟩

theorem presented_availability_without_faithful_consumption :
    neutralizingUptake.PresentedInputAvailable false true actualInput ∧
    ¬ neutralizingUptake.FaithfullyConsumes false true actualInput ∧
    ¬ FunctionalUptake coherenceFrame parityAction neutralizingUptake
      false true := by
  refine ⟨⟨alternateInput, rfl⟩, ?_, neutralizing_uptake_has_no_r3⟩
  intro consumes
  have equal := Option.some.inj consumes
  cases equal

theorem forecast_consumption_without_de_se_dependence :
    forecastOnlyUptake.run false true actualInput = some PUnit.unit ∧
    FactorsThroughDeSeErasure forecastOnlyUptake false true ∧
    ¬ FunctionalUptake coherenceFrame parityAction forecastOnlyUptake
      false true := by
  exact ⟨rfl, forecast_only_factors_through_erasure,
    forecast_only_has_no_r3⟩

theorem faithful_forecast_consumption_still_not_de_se_uptake :
    forecastOnlyUptake.FaithfullyConsumes false true actualInput ∧
    FactorsThroughDeSeErasure forecastOnlyUptake false true ∧
    ¬ FunctionalUptake coherenceFrame parityAction forecastOnlyUptake
      false true := by
  exact ⟨rfl, forecast_only_factors_through_erasure,
    forecast_only_has_no_r3⟩

def OutputCorrect (output : Bool) : Prop := output = false

theorem de_se_dependence_without_success :
    FunctionalUptake coherenceFrame parityAction faithfulUptake false true ∧
    faithfulUptake.run false true coherenceAvailable.input = some true ∧
    ¬ OutputCorrect true := by
  exact ⟨faithful_uptake_has_r3, rfl, fun correct => Bool.noConfusion correct⟩

theorem successful_output_without_uptake :
    constantUptake.run false true coherenceAvailable.input = some false ∧
    OutputCorrect false ∧
    ¬ FunctionalUptake coherenceFrame parityAction constantUptake false true := by
  exact ⟨rfl, rfl, constant_uptake_has_no_r3⟩

/-! Record, continuation, R1, and grounding separations. -/

def mnemonicConstantUptake : UptakeLayer mnemonicCoherenceFrame
    mnemonicFixedAction where
  Output := PUnit
  present := fun _ _ input => some input
  present_erasure := by
    intro c d input supplied presented
    exact congrArg ProspectiveFunctionalInput.eraseDeSe
      (Option.some.inj presented.symm)
  present_lawful := by
    intro c d input supplied lawful presented
    rw [Option.some.inj presented.symm]
    exact lawful
  evaluate := fun _ _ _ => PUnit.unit

theorem mnemonic_records_without_uptake :
    MemoryAttributed mnemonicCoherenceRepresentation (.atlas true false) ∧
    mnemonicCoherenceInformation.traceValid PUnit.unit ∧
    ¬ FunctionalUptake mnemonicCoherenceFrame mnemonicFixedAction
      mnemonicConstantUptake false true := by
  refine ⟨⟨rfl, ⟨PUnit.unit, True.intro⟩⟩, True.intro, ?_⟩
  intro uptake
  exact mnemonic_fixed_action_has_no_r2
    (functional_uptake_implies_r2 uptake)

def fixedConstantUptake : UptakeLayer coherenceFrame fixedAction where
  Output := PUnit
  present := fun _ _ input => some input
  present_erasure := by
    intro c d input supplied presented
    exact congrArg ProspectiveFunctionalInput.eraseDeSe
      (Option.some.inj presented.symm)
  present_lawful := by
    intro c d input supplied lawful presented
    rw [Option.some.inj presented.symm]
    exact lawful
  evaluate := fun _ _ _ => PUnit.unit

theorem r1_without_uptake :
    InternalRoleEncoding coherenceRepresentation false true ∧
    ¬ FunctionalUptake coherenceFrame fixedAction fixedConstantUptake
      false true := by
  refine ⟨coherence_representation_has_r1, ?_⟩
  intro uptake
  exact fixed_action_has_no_r2 (functional_uptake_implies_r2 uptake)

theorem continuation_without_uptake :
    coherenceRepresentation.continuationCandidate false true ∧
    ¬ FunctionalUptake coherenceFrame fixedAction fixedConstantUptake
      false true := by
  exact ⟨.candidate, r1_without_uptake.2⟩

theorem forecast_grounding_without_uptake :
    coherenceRepresentation.groundedByForecast
      (.reference false true true) PUnit.unit ∧
    ¬ FunctionalUptake coherenceFrame parityAction constantUptake false true := by
  exact ⟨.target true, constant_uptake_has_no_r3⟩

/-! A three-center fixture supplies two actual R2 inputs in one literal frame
    and action.  This is separate from the critical presentation-only pair. -/

inductive ThreeCenter
  | source | left | right
  deriving Repr

inductive ThreeBefore : ThreeCenter → ThreeCenter → Prop
  | left : ThreeBefore .source .left
  | right : ThreeBefore .source .right

theorem threeBefore_irrefl : Irreflexive ThreeBefore := by
  intro center before
  cases before

theorem threeBefore_trans : Transitive ThreeBefore := by
  intro a b c ab bc
  cases ab <;> cases bc

def threeBase : StaticBase.{0, 0, 0} where
  Event := ThreeCenter
  Observer := PUnit
  Center := ThreeCenter
  causal := ThreeBefore
  causal_irrefl := threeBefore_irrefl
  causal_trans := threeBefore_trans
  owner := fun _ => PUnit.unit
  «at» := fun center => center

def threeInformation : InformationLayer.{0, 0, 0, 0, 0, 0} threeBase where
  Stage := ThreeCenter
  actualStage := fun center => center
  stageAt := fun stage => stage
  stageAt_actual := fun _ => rfl
  RecordToken := Empty
  recordAt := fun record => nomatch record
  recordSource := fun record => nomatch record
  recordAbout := fun record => nomatch record
  traceValid := fun record => nomatch record
  ForecastToken := Bool
  forecastAt := fun _ => .source
  forecastTarget
    | false => .left
    | true => .right

inductive ThreeNode
  | atlas (evaluation target : ThreeCenter)
  | reference (host represented : ThreeCenter) (ref : Bool)
  deriving Repr

def threeRole : ThreeCenter → ThreeCenter → CenterRole
  | .source, .source => .current
  | .source, .left => .future
  | .source, .right => .future
  | .left, .source => .past
  | .left, .left => .current
  | .left, .right => .current
  | .right, .source => .past
  | .right, .left => .current
  | .right, .right => .current

def centerBit : ThreeCenter → Bool
  | .source => false
  | .left => false
  | .right => true

def xor : Bool → Bool → Bool
  | false, value => value
  | true, false => true
  | true, true => false

def threeCarry (a b : ThreeCenter) (ref : Bool) : Bool :=
  xor (xor ref (centerBit a)) (centerBit b)

inductive ThreeContinuation : ThreeCenter → ThreeCenter → Prop
  | left : ThreeContinuation .source .left
  | right : ThreeContinuation .source .right

inductive ThreeReferenceBefore : ThreeNode → ThreeNode → Prop
  | left (ref : Bool) : ThreeReferenceBefore
      (.reference .source .source ref)
      (.reference .source .left (threeCarry .source .left ref))
  | right (ref : Bool) : ThreeReferenceBefore
      (.reference .source .source ref)
      (.reference .source .right (threeCarry .source .right ref))

inductive ThreeGrounding : ThreeNode → Bool → Prop
  | left (ref : Bool) : ThreeGrounding (.reference .source .left ref) false
  | right (ref : Bool) : ThreeGrounding (.reference .source .right ref) true

def threeRepresentation : RepresentationLayer threeInformation where
  RepNode := ThreeNode
  nodeStage
    | .atlas _ _ => .source
    | .reference host _ _ => host
  perspective
    | .atlas evaluation _ => some evaluation
    | .reference _ represented _ => some represented
  target
    | .atlas _ target => some target
    | .reference _ represented _ => some represented
  encodedRole
    | .atlas evaluation target => threeRole evaluation target
    | .reference _ _ _ => .current
  mode := fun _ => .neutral
  repBefore := ThreeReferenceBefore
  groundedByRecord := fun _ record => nomatch record
  groundedByForecast := ThreeGrounding
  continuationCandidate := ThreeContinuation

theorem source_left_external : ExternalRoleShift threeBase .source .left := by
  exact ⟨rfl, ⟨rfl, .left⟩, rfl, ⟨rfl, .left⟩,
    ⟨rfl, .left⟩, rfl⟩

theorem source_right_external : ExternalRoleShift threeBase .source .right := by
  exact ⟨rfl, ⟨rfl, .right⟩, rfl, ⟨rfl, .right⟩,
    ⟨rfl, .right⟩, rfl⟩

theorem source_left_r1 : InternalRoleEncoding threeRepresentation
    .source .left := by
  exact ⟨source_left_external,
    ⟨.atlas .source .source, rfl, rfl, rfl, rfl⟩,
    ⟨.atlas .source .left, rfl, rfl, rfl, rfl⟩,
    ⟨.atlas .left .source, rfl, rfl, rfl, rfl⟩,
    ⟨.atlas .left .left, rfl, rfl, rfl, rfl⟩⟩

theorem source_right_r1 : InternalRoleEncoding threeRepresentation
    .source .right := by
  exact ⟨source_right_external,
    ⟨.atlas .source .source, rfl, rfl, rfl, rfl⟩,
    ⟨.atlas .source .right, rfl, rfl, rfl, rfl⟩,
    ⟨.atlas .right .source, rfl, rfl, rfl, rfl⟩,
    ⟨.atlas .right .right, rfl, rfl, rfl, rfl⟩⟩

def threeFrame : SelfReferenceFrame threeRepresentation where
  Reference := Bool
  referenceNode := ThreeNode.reference
  currentReference := centerBit
  referenceNode_injective := by
    intro host represented a b equal
    cases equal
    rfl
  nodeStage_reference := by intro host represented ref; rfl
  perspective_reference := by intro host represented ref; rfl
  target_reference := by intro host represented ref; rfl
  role_reference := by intro host represented ref; rfl
  grounding_coordinates := by
    intro host represented ref forecast grounded
    cases grounded <;> exact ⟨rfl, rfl⟩

def threeAction : CoherentReferenceAction threeFrame where
  carry := threeCarry
  carry_refl := by
    intro center ref
    cases center <;> cases ref <;> rfl
  carry_comp := by
    intro a b c ref
    cases a <;> cases b <;> cases c <;> cases ref <;> rfl
  continuation_before := by
    intro c d ref continuation
    cases continuation
    · exact .left ref
    · exact .right ref

def leftAvailable : AvailableProspectiveEncoding threeFrame threeAction
    .source .left where
  roleEncoding := source_left_r1
  continuation := .left
  preservation := rfl
  forecast := false
  hosted := ⟨rfl, rfl⟩
  grounded := .left false

def rightAvailable : AvailableProspectiveEncoding threeFrame threeAction
    .source .right where
  roleEncoding := source_right_r1
  continuation := .right
  preservation := rfl
  forecast := true
  hosted := ⟨rfl, rfl⟩
  grounded := .right true

def threeFaithfulUptake : UptakeLayer threeFrame threeAction where
  Output := Bool
  present := fun _ _ input => some input
  present_erasure := by
    intro c d input supplied presented
    exact congrArg ProspectiveFunctionalInput.eraseDeSe
      (Option.some.inj presented.symm)
  present_lawful := by
    intro c d input supplied lawful presented
    rw [Option.some.inj presented.symm]
    exact lawful
  evaluate := fun _ _ input => input.reference

def threeConstantUptake : UptakeLayer threeFrame threeAction where
  Output := Bool
  present := fun _ _ input => some input
  present_erasure := by
    intro c d input supplied presented
    exact congrArg ProspectiveFunctionalInput.eraseDeSe
      (Option.some.inj presented.symm)
  present_lawful := by
    intro c d input supplied lawful presented
    rw [Option.some.inj presented.symm]
    exact lawful
  evaluate := fun _ _ _ => true

def leftAlternate : ProspectiveFunctionalInput threeFrame .source .left where
  reference := true
  forecast := false

def rightAlternate : ProspectiveFunctionalInput threeFrame .source .right where
  reference := false
  forecast := true

theorem left_alternate_lawful :
    LawfulProspectiveInput threeFrame .source .left leftAlternate := by
  exact ⟨⟨rfl, rfl⟩, .left true⟩

theorem right_alternate_lawful :
    LawfulProspectiveInput threeFrame .source .right rightAlternate := by
  exact ⟨⟨rfl, rfl⟩, .right false⟩

theorem left_input_has_r3 :
    FunctionalUptake threeFrame threeAction threeFaithfulUptake
      .source .left := by
  refine ⟨leftAvailable.toR2, leftAvailable.input, leftAlternate,
    leftAvailable.input_lawful, left_alternate_lawful,
    rfl, rfl, ?_, rfl, rfl, ?_⟩
  · intro equal
    cases equal
  · intro equal
    cases equal

theorem right_input_has_r3 :
    FunctionalUptake threeFrame threeAction threeFaithfulUptake
      .source .right := by
  refine ⟨rightAvailable.toR2, rightAvailable.input, rightAlternate,
    rightAvailable.input_lawful, right_alternate_lawful,
    rfl, rfl, ?_, rfl, rfl, ?_⟩
  · intro equal
    cases equal
  · intro equal
    cases equal

theorem three_constant_factors (c d : threeBase.Center) :
    FactorsThroughDeSeErasure threeConstantUptake c d := by
  refine ⟨fun _ => some true, ?_⟩
  intro input lawful
  rfl

theorem three_constant_has_no_r3 (c d : threeBase.Center) :
    ¬ FunctionalUptake threeFrame threeAction threeConstantUptake c d := by
  intro uptake
  exact (functional_uptake_not_factors_through_erasure uptake)
    (three_constant_factors c d)

theorem two_r2_inputs_have_distinct_functional_consequences :
    ProspectiveDeSeEncoding threeFrame threeAction .source .left ∧
    ProspectiveDeSeEncoding threeFrame threeAction .source .right ∧
    threeFaithfulUptake.run .source .left leftAvailable.input = some false ∧
    threeFaithfulUptake.run .source .right rightAvailable.input = some true := by
  exact ⟨leftAvailable.toR2, rightAvailable.toR2, rfl, rfl⟩

theorem distinct_r2_inputs_can_have_same_functional_output :
    ProspectiveDeSeEncoding threeFrame threeAction .source .left ∧
    ProspectiveDeSeEncoding threeFrame threeAction .source .right ∧
    threeConstantUptake.run .source .left leftAvailable.input =
      threeConstantUptake.run .source .right rightAvailable.input := by
  exact ⟨leftAvailable.toR2, rightAvailable.toR2, rfl⟩

theorem two_r2_inputs_each_have_r3_and_distinct_results :
    FunctionalUptake threeFrame threeAction threeFaithfulUptake
        .source .left ∧
    FunctionalUptake threeFrame threeAction threeFaithfulUptake
        .source .right ∧
    threeFaithfulUptake.run .source .left leftAvailable.input = some false ∧
    threeFaithfulUptake.run .source .right rightAvailable.input = some true := by
  exact ⟨left_input_has_r3, right_input_has_r3, rfl, rfl⟩

theorem distinct_r2_inputs_same_output_without_r3 :
    ProspectiveDeSeEncoding threeFrame threeAction .source .left ∧
    ProspectiveDeSeEncoding threeFrame threeAction .source .right ∧
    threeConstantUptake.run .source .left leftAvailable.input =
      threeConstantUptake.run .source .right rightAvailable.input ∧
    ¬ FunctionalUptake threeFrame threeAction threeConstantUptake
        .source .left ∧
    ¬ FunctionalUptake threeFrame threeAction threeConstantUptake
        .source .right := by
  exact ⟨leftAvailable.toR2, rightAvailable.toR2, rfl,
    three_constant_has_no_r3 .source .left,
    three_constant_has_no_r3 .source .right⟩

end StaticRole.Countermodels.UptakeHostiles
