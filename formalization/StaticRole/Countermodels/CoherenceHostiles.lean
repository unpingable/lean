/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE
-/

import StaticRole.Model.Expansion

namespace StaticRole.Countermodels.CoherenceHostiles

/-! A self-contained finite phase-two fixture.  The positive and negative
    actions below share the base, information layer, representation layer,
    reference frame, current-reference section, and every node-level fact. -/

inductive CausalBefore : Bool → Bool → Prop
  | edge : CausalBefore false true

theorem causalBefore_irrefl : Irreflexive CausalBefore := by
  intro value beforeSelf
  cases beforeSelf

theorem causalBefore_trans : Transitive CausalBefore := by
  intro first middle last firstBeforeMiddle middleBeforeLast
  cases firstBeforeMiddle
  cases middleBeforeLast

def coherenceBase : StaticBase.{0, 0, 0} where
  Event := Bool
  Observer := PUnit
  Center := Bool
  causal := CausalBefore
  causal_irrefl := causalBefore_irrefl
  causal_trans := causalBefore_trans
  owner := fun _ => PUnit.unit
  «at» := fun center => center

theorem coherence_center_before :
    CenterBefore coherenceBase false true := by
  exact ⟨rfl, .edge⟩

theorem coherence_external_role_shift :
    ExternalRoleShift coherenceBase false true := by
  exact ⟨rfl, coherence_center_before, rfl, coherence_center_before,
    coherence_center_before, rfl⟩

/-- The central reduct has one forecast and constructively no record token. -/
def coherenceInformation :
    InformationLayer.{0, 0, 0, 0, 0, 0} coherenceBase where
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

/-- Atlas nodes provide R1.  Reference nodes realize a two-point reference
    fiber at every host/represented-center pair. -/
inductive CoherenceNode
  | atlas (evaluation target : Bool)
  | reference (host represented ref : Bool)
  deriving Repr

def atlasRole : Bool → Bool → CenterRole
  | false, false => .current
  | false, true => .future
  | true, false => .past
  | true, true => .current

inductive ContinuationPair : Bool → Bool → Prop
  | candidate : ContinuationPair false true

/-- The graph deliberately admits both perfect matchings between the source
    and destination reference fibers.  A lawful action must select one
    globally coherently. -/
inductive ReferenceBefore : CoherenceNode → CoherenceNode → Prop
  | edge (sourceRef targetRef : Bool) :
      ReferenceBefore
        (.reference false false sourceRef)
        (.reference false true targetRef)

/-- Both target-fiber nodes have exactly the same forecast provenance. -/
inductive ForecastGrounding : CoherenceNode → PUnit → Prop
  | target (ref : Bool) :
      ForecastGrounding (.reference false true ref) PUnit.unit

def coherenceRepresentation : RepresentationLayer coherenceInformation where
  RepNode := CoherenceNode
  nodeStage
    | .atlas _ _ => false
    | .reference host _ _ => host
  perspective
    | .atlas evaluation _ => some evaluation
    | .reference _ represented _ => some represented
  target
    | .atlas _ target => some target
    | .reference _ represented _ => some represented
  encodedRole
    | .atlas evaluation target => atlasRole evaluation target
    | .reference _ _ _ => .current
  mode := fun _ => .neutral
  repBefore := ReferenceBefore
  groundedByRecord := fun _ record => nomatch record
  groundedByForecast := ForecastGrounding
  continuationCandidate := ContinuationPair

theorem coherence_representation_has_r1 :
    InternalRoleEncoding coherenceRepresentation false true := by
  exact ⟨coherence_external_role_shift,
    ⟨.atlas false false, rfl, rfl, rfl, rfl⟩,
    ⟨.atlas false true, rfl, rfl, rfl, rfl⟩,
    ⟨.atlas true false, rfl, rfl, rfl, rfl⟩,
    ⟨.atlas true true, rfl, rfl, rfl, rfl⟩⟩

/-- The current section varies with the represented center: false at the
    first center and true at the second. -/
def coherenceFrame : SelfReferenceFrame coherenceRepresentation where
  Reference := Bool
  referenceNode := CoherenceNode.reference
  currentReference := fun center => center
  referenceNode_injective := by
    intro host represented left right equal
    cases equal
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
    intro host represented ref forecast grounded
    cases grounded
    exact ⟨rfl, rfl⟩

def flip : Bool → Bool
  | false => true
  | true => false

/-- Endpoint parity is the nontrivial flat action on the two-point fiber. -/
def parityCarry : Bool → Bool → Bool → Bool
  | false, false, ref => ref
  | false, true, ref => flip ref
  | true, false, ref => flip ref
  | true, true, ref => ref

/-- The fixed action is the other lawful action on the exact same frame. -/
def fixedCarry (_source _target : Bool) (ref : Bool) : Bool := ref

def parityAction : CoherentReferenceAction coherenceFrame where
  carry := parityCarry
  carry_refl := by
    intro center ref
    cases center <;> rfl
  carry_comp := by
    intro a b c ref
    cases a <;> cases b <;> cases c <;> cases ref <;> rfl
  continuation_before := by
    intro c d ref continuation
    cases continuation
    exact .edge ref (parityCarry false true ref)

def fixedAction : CoherentReferenceAction coherenceFrame where
  carry := fixedCarry
  carry_refl := by
    intro center ref
    rfl
  carry_comp := by
    intro a b c ref
    rfl
  continuation_before := by
    intro c d ref continuation
    cases continuation
    exact .edge ref ref

/-- Two explicit lawful expansions over the exact same dependent lower-level
    reduct.  Their representation and frame fields are definitionally the
    same terms; only the lawful action differs. -/
def parityExpansion : CoherentExpansion coherenceInformation where
  representation := coherenceRepresentation
  referenceFrame := coherenceFrame
  referenceAction := parityAction

def fixedExpansion : CoherentExpansion coherenceInformation where
  representation := coherenceRepresentation
  referenceFrame := coherenceFrame
  referenceAction := fixedAction

theorem parity_action_preserves_current_reference :
    PreservesCurrentReference coherenceFrame parityAction false true := by
  rfl

theorem fixed_action_does_not_preserve_current_reference :
    ¬ PreservesCurrentReference coherenceFrame fixedAction false true := by
  intro preservation
  change false = true at preservation
  cases preservation

theorem parity_action_has_r2 :
    ProspectiveDeSeEncoding coherenceFrame parityAction false true := by
  exact ⟨coherence_representation_has_r1, .candidate, rfl,
    PUnit.unit, ⟨rfl, rfl⟩, .target true⟩

theorem fixed_action_has_no_r2 :
    ¬ ProspectiveDeSeEncoding coherenceFrame fixedAction false true := by
  intro r2
  exact fixed_action_does_not_preserve_current_reference r2.2.2.1

theorem parity_action_has_coherent_witness :
    Nonempty (CoherentProspectiveWitness
      coherenceFrame parityAction false true) := by
  exact (prospective_de_se_iff_coherent_transport.mp
    parity_action_has_r2).2

theorem fixed_action_has_no_coherent_witness :
    ¬ Nonempty (CoherentProspectiveWitness
      coherenceFrame fixedAction false true) := by
  intro witness
  apply fixed_action_has_no_r2
  exact prospective_de_se_iff_coherent_transport.mpr
    ⟨coherence_representation_has_r1, witness⟩

/-- The negative action still meets every R2 condition other than transport
    of the fixed current-reference section. -/
theorem fixed_action_satisfies_all_neighboring_conditions :
    InternalRoleEncoding coherenceRepresentation false true ∧
    coherenceRepresentation.continuationCandidate false true ∧
    ForecastHostedFor coherenceInformation PUnit.unit false true ∧
    coherenceRepresentation.groundedByForecast
      (coherenceFrame.referenceNode false true
        (fixedAction.carry false true
          (coherenceFrame.currentReference false)))
      PUnit.unit := by
  exact ⟨coherence_representation_has_r1, .candidate, ⟨rfl, rfl⟩,
    .target false⟩

theorem central_actions_separate_only_at_carried_reference :
    parityAction.carry false true
        (coherenceFrame.currentReference false) = true ∧
    fixedAction.carry false true
        (coherenceFrame.currentReference false) = false := by
  exact ⟨rfl, rfl⟩

/-- The critical same-reduct separation.  Both terms inhabit the action type
    over the one literal `coherenceFrame`; no representation field changes. -/
theorem same_reduct_lawful_actions_disagree_on_r2 :
    ProspectiveDeSeEncoding coherenceFrame parityAction false true ∧
    ¬ ProspectiveDeSeEncoding coherenceFrame fixedAction false true := by
  exact ⟨parity_action_has_r2, fixed_action_has_no_r2⟩

theorem same_reduct_lawful_actions_disagree_on_coherent_transport :
    Nonempty (CoherentProspectiveWitness
        coherenceFrame parityAction false true) ∧
    ¬ Nonempty (CoherentProspectiveWitness
        coherenceFrame fixedAction false true) := by
  exact ⟨parity_action_has_coherent_witness,
    fixed_action_has_no_coherent_witness⟩

/-- Action-independent receipts for the lower-level structure shared by both
    halves of the central pair. -/
theorem central_pair_shared_facts :
    InternalRoleEncoding coherenceRepresentation false true ∧
    coherenceRepresentation.continuationCandidate false true ∧
    CurrentSelfNode coherenceFrame false
      (.reference false false false) ∧
    ProjectedSelfNode coherenceFrame false true
      (.reference false true true) ∧
    coherenceRepresentation.groundedByForecast
      (.reference false true false) PUnit.unit ∧
    coherenceRepresentation.groundedByForecast
      (.reference false true true) PUnit.unit := by
  exact ⟨coherence_representation_has_r1, .candidate, rfl, rfl,
    .target false, .target true⟩

theorem r2_without_record_tokens :
    ProspectiveDeSeEncoding coherenceFrame parityAction false true ∧
    (∀ _record : coherenceInformation.RecordToken, False) := by
  exact ⟨parity_action_has_r2, fun record => nomatch record⟩

/-! Hostile separations reusing the central pair. -/

theorem r1_without_self_reference_transport :
    InternalRoleEncoding coherenceRepresentation false true ∧
    ¬ Nonempty (CoherentProspectiveWitness
      coherenceFrame fixedAction false true) := by
  exact ⟨coherence_representation_has_r1,
    fixed_action_has_no_coherent_witness⟩

theorem continuation_without_self_reference_preservation :
    coherenceRepresentation.continuationCandidate false true ∧
    ¬ PreservesCurrentReference coherenceFrame fixedAction false true := by
  exact ⟨.candidate, fixed_action_does_not_preserve_current_reference⟩

theorem anchors_without_preserving_transport :
    CurrentSelfNode coherenceFrame false
        (.reference false false false) ∧
    ProjectedSelfNode coherenceFrame false true
        (.reference false true true) ∧
    ¬ PreservesCurrentReference coherenceFrame fixedAction false true := by
  exact ⟨rfl, rfl, fixed_action_does_not_preserve_current_reference⟩

/-- Removing only the representation edge leaves both canonical anchors but
    makes a lawful action impossible: its continuation law would have to
    construct an inhabitant of `False`. -/
def disconnectedRepresentation : RepresentationLayer coherenceInformation :=
  { coherenceRepresentation with
    repBefore := fun _ _ => False }

def disconnectedFrame : SelfReferenceFrame disconnectedRepresentation where
  Reference := Bool
  referenceNode := CoherenceNode.reference
  currentReference := fun center => center
  referenceNode_injective := by
    intro host represented left right equal
    cases equal
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
    intro host represented ref forecast grounded
    cases grounded
    exact ⟨rfl, rfl⟩

theorem current_and_projected_anchors_without_any_lawful_action :
    InternalRoleEncoding disconnectedRepresentation false true ∧
    CurrentSelfNode disconnectedFrame false
      (.reference false false false) ∧
    ProjectedSelfNode disconnectedFrame false true
      (.reference false true true) ∧
    ¬ Nonempty (CoherentReferenceAction disconnectedFrame) := by
  refine ⟨?_, rfl, rfl, ?_⟩
  · exact ⟨coherence_external_role_shift,
      ⟨.atlas false false, rfl, rfl, rfl, rfl⟩,
      ⟨.atlas false true, rfl, rfl, rfl, rfl⟩,
      ⟨.atlas true false, rfl, rfl, rfl, rfl⟩,
      ⟨.atlas true true, rfl, rfl, rfl, rfl⟩⟩
  · rintro ⟨action⟩
    exact action.continuation_before false true false .candidate

theorem forecast_grounding_without_self_reference_transport :
    ForecastHostedFor coherenceInformation PUnit.unit false true ∧
    coherenceRepresentation.groundedByForecast
      (.reference false true true) PUnit.unit ∧
    ¬ ProspectiveDeSeEncoding coherenceFrame fixedAction false true := by
  exact ⟨⟨rfl, rfl⟩, .target true, fixed_action_has_no_r2⟩

/-! A lawful, anchor-preserving action and represented succession remain
    insufficient when the forecast-grounding relation alone is removed. -/

def ungroundedRepresentation : RepresentationLayer coherenceInformation :=
  { coherenceRepresentation with
    groundedByForecast := fun _ _ => False }

def ungroundedFrame : SelfReferenceFrame ungroundedRepresentation where
  Reference := Bool
  referenceNode := CoherenceNode.reference
  currentReference := fun center => center
  referenceNode_injective := by
    intro host represented left right equal
    cases equal
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
    intro host represented ref forecast grounded
    exact grounded.elim

def ungroundedParityAction : CoherentReferenceAction ungroundedFrame where
  carry := parityCarry
  carry_refl := by
    intro center ref
    cases center <;> rfl
  carry_comp := by
    intro a b c ref
    cases a <;> cases b <;> cases c <;> cases ref <;> rfl
  continuation_before := by
    intro c d ref continuation
    cases continuation
    exact .edge ref (parityCarry false true ref)

theorem ungrounded_representation_has_r1 :
    InternalRoleEncoding ungroundedRepresentation false true := by
  exact ⟨coherence_external_role_shift,
    ⟨.atlas false false, rfl, rfl, rfl, rfl⟩,
    ⟨.atlas false true, rfl, rfl, rfl, rfl⟩,
    ⟨.atlas true false, rfl, rfl, rfl, rfl⟩,
    ⟨.atlas true true, rfl, rfl, rfl, rfl⟩⟩

theorem lawful_succession_without_forecast_grounding :
    PreservesCurrentReference ungroundedFrame ungroundedParityAction
        false true ∧
    ungroundedRepresentation.continuationCandidate false true ∧
    ungroundedRepresentation.repBefore
      (.reference false false false) (.reference false true true) ∧
    ForecastHostedFor coherenceInformation PUnit.unit false true ∧
    ¬ ProspectiveDeSeEncoding
      ungroundedFrame ungroundedParityAction false true := by
  refine ⟨rfl, .candidate, .edge false true, ⟨rfl, rfl⟩, ?_⟩
  intro r2
  obtain ⟨forecast, hosted, grounded⟩ := r2.2.2.2
  exact grounded

/-! Accurate reference endpoints do not repair a mislabelled R1 atlas. -/

def misroleRepresentation : RepresentationLayer coherenceInformation :=
  { coherenceRepresentation with
    encodedRole := fun _ => .current }

def misroleFrame : SelfReferenceFrame misroleRepresentation where
  Reference := Bool
  referenceNode := CoherenceNode.reference
  currentReference := fun center => center
  referenceNode_injective := by
    intro host represented left right equal
    cases equal
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
    intro host represented ref forecast grounded
    cases grounded
    exact ⟨rfl, rfl⟩

def misroleParityAction : CoherentReferenceAction misroleFrame where
  carry := parityCarry
  carry_refl := by
    intro center ref
    cases center <;> rfl
  carry_comp := by
    intro a b c ref
    cases a <;> cases b <;> cases c <;> cases ref <;> rfl
  continuation_before := by
    intro c d ref continuation
    cases continuation
    exact .edge ref (parityCarry false true ref)

theorem misrole_does_not_encode_future :
    ¬ Encodes misroleRepresentation false false true .future := by
  rintro ⟨node, atHost, perspective, target, role⟩
  cases node <;> exact CenterRole.noConfusion role

theorem misrole_future_cell_is_inaccurate :
    ¬ AccurateEncoding misroleRepresentation (.atlas false true) := by
  rintro ⟨evaluation, target, perspectiveEq, targetEq, external⟩
  have evaluationEq : evaluation = false :=
    (Option.some.inj perspectiveEq).symm
  have targetCenterEq : target = true :=
    (Option.some.inj targetEq).symm
  rw [evaluationEq, targetCenterEq] at external
  change false = true at external
  cases external

theorem self_reference_transport_with_inaccurate_role_encoding :
    PreservesCurrentReference misroleFrame misroleParityAction false true ∧
    misroleRepresentation.continuationCandidate false true ∧
    ForecastHostedFor coherenceInformation PUnit.unit false true ∧
    misroleRepresentation.groundedByForecast
      (.reference false true true) PUnit.unit ∧
    ¬ AccurateEncoding misroleRepresentation (.atlas false true) ∧
    ¬ ProspectiveDeSeEncoding misroleFrame misroleParityAction false true := by
  refine ⟨rfl, .candidate, ⟨rfl, rfl⟩, .target true,
    misrole_future_cell_is_inaccurate, ?_⟩
  intro r2
  exact misrole_does_not_encode_future r2.1.2.2.1

/-- A local endpoint mapping can look correct while failing the unconditional
    identity law required of every lawful action. -/
def locallyCorrectButIncoherentCarry : Bool → Bool → Bool → Bool
  | false, true, _ => true
  | false, false, _ => false
  | true, false, _ => false
  | true, true, _ => false

theorem locally_correct_endpoint :
    locallyCorrectButIncoherentCarry false true
        (coherenceFrame.currentReference false) =
      coherenceFrame.currentReference true := by
  rfl

theorem locally_incoherent_identity :
    ¬ (∀ center ref,
      locallyCorrectButIncoherentCarry center center ref = ref) := by
  intro identity
  have falseEqTrue : (false : Bool) = true := identity false true
  exact Bool.noConfusion falseEqTrue

theorem transport_shaped_pair_without_identity_coherence :
    locallyCorrectButIncoherentCarry false true
        (coherenceFrame.currentReference false) =
      coherenceFrame.currentReference true ∧
    coherenceRepresentation.repBefore
      (.reference false false false) (.reference false true true) ∧
    ¬ (∀ center ref,
      locallyCorrectButIncoherentCarry center center ref = ref) := by
  exact ⟨locally_correct_endpoint, .edge false true,
    locally_incoherent_identity⟩

/-! Valid record provenance and mnemonic annotation remain orthogonal to the
    anchor-preserving prospective bridge. -/

def mnemonicCoherenceInformation :
    InformationLayer.{0, 0, 0, 0, 0, 0} coherenceBase where
  Stage := Bool
  actualStage := fun center => center
  stageAt := fun stage => stage
  stageAt_actual := fun _ => rfl
  RecordToken := PUnit
  recordAt := fun _ => false
  recordSource := fun _ => false
  recordAbout := fun _ => true
  traceValid := fun _ => True
  ForecastToken := PUnit
  forecastAt := fun _ => false
  forecastTarget := fun _ => true

def mnemonicCoherenceRepresentation :
    RepresentationLayer mnemonicCoherenceInformation where
  RepNode := CoherenceNode
  nodeStage
    | .atlas _ _ => false
    | .reference host _ _ => host
  perspective
    | .atlas evaluation _ => some evaluation
    | .reference _ represented _ => some represented
  target
    | .atlas _ target => some target
    | .reference _ represented _ => some represented
  encodedRole
    | .atlas evaluation target => atlasRole evaluation target
    | .reference _ _ _ => .current
  mode := fun _ => .mnemonic
  repBefore := ReferenceBefore
  groundedByRecord := fun _ _ => True
  groundedByForecast := ForecastGrounding
  continuationCandidate := ContinuationPair

def mnemonicCoherenceFrame :
    SelfReferenceFrame mnemonicCoherenceRepresentation where
  Reference := Bool
  referenceNode := CoherenceNode.reference
  currentReference := fun center => center
  referenceNode_injective := by
    intro host represented left right equal
    cases equal
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
    intro host represented ref forecast grounded
    cases grounded
    exact ⟨rfl, rfl⟩

def mnemonicFixedAction :
    CoherentReferenceAction mnemonicCoherenceFrame where
  carry := fixedCarry
  carry_refl := by
    intro center ref
    rfl
  carry_comp := by
    intro a b c ref
    rfl
  continuation_before := by
    intro c d ref continuation
    cases continuation
    exact .edge ref ref

theorem mnemonic_fixed_action_has_no_r2 :
    ¬ ProspectiveDeSeEncoding
      mnemonicCoherenceFrame mnemonicFixedAction false true := by
  intro r2
  have preservation := r2.2.2.1
  change false = true at preservation
  cases preservation

theorem mnemonic_record_grounding_without_prospective_de_se :
    MemoryAttributed mnemonicCoherenceRepresentation
      (.atlas true false) ∧
    mnemonicCoherenceInformation.traceValid PUnit.unit ∧
    mnemonicCoherenceInformation.recordSource PUnit.unit = false ∧
    mnemonicCoherenceInformation.recordAbout PUnit.unit = true ∧
    ¬ ProspectiveDeSeEncoding
      mnemonicCoherenceFrame mnemonicFixedAction false true := by
  exact ⟨⟨rfl, ⟨PUnit.unit, True.intro⟩⟩, True.intro, rfl, rfl,
    mnemonic_fixed_action_has_no_r2⟩

/-- Phase three remains deliberately unimplemented. -/
def FunctionalUptakePlaceholder
    (_F : SelfReferenceFrame coherenceRepresentation)
    (_A : CoherentReferenceAction _F)
    (_c _d : coherenceBase.Center) : Prop := False

theorem r2_without_functional_uptake :
    ProspectiveDeSeEncoding coherenceFrame parityAction false true ∧
    ¬ FunctionalUptakePlaceholder coherenceFrame parityAction false true := by
  exact ⟨parity_action_has_r2, fun uptake => uptake⟩

end StaticRole.Countermodels.CoherenceHostiles
