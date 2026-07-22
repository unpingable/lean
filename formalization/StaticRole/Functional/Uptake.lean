/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE
-/

import StaticRole.Representation.DeSeProjection

namespace StaticRole

universe uE uO uC uS uR uF uN uA uU

/-- The exact computational payload made available to a bounded downstream
    transition.  Source and target centers are type indices.  The realized
    node and its current role are derived from the frame, rather than copied
    into a second potentially divergent representation. -/
structure ProspectiveFunctionalInput
    {B : StaticBase.{uE, uO, uC}}
    {I : InformationLayer.{uE, uO, uC, uS, uR, uF} B}
    {R : RepresentationLayer.{uE, uO, uC, uS, uR, uF, uN} I}
    (F : SelfReferenceFrame.{uA} R)
    (_c _d : B.Center) where
  reference : F.Reference
  forecast : I.ForecastToken

namespace ProspectiveFunctionalInput

/-- The node determined by the input's reference coordinate. -/
def node
    {B : StaticBase} {I : InformationLayer B}
    {R : RepresentationLayer I}
    {F : SelfReferenceFrame R}
    {c d : B.Center}
    (input : ProspectiveFunctionalInput F c d) : R.RepNode :=
  F.referenceNode c d input.reference

/-- Erase exactly the de se coordinate, retaining the forecast context. -/
def eraseDeSe
    {B : StaticBase} {I : InformationLayer B}
    {R : RepresentationLayer I}
    {F : SelfReferenceFrame R}
    {c d : B.Center}
    (input : ProspectiveFunctionalInput F c d) : I.ForecastToken :=
  input.forecast

/-- Two inputs are equal when both computational coordinates agree. -/
theorem ext
    {B : StaticBase} {I : InformationLayer B}
    {R : RepresentationLayer I}
    {F : SelfReferenceFrame R}
    {c d : B.Center}
    {left right : ProspectiveFunctionalInput F c d}
    (reference : left.reference = right.reference)
    (forecast : left.forecast = right.forecast) : left = right := by
  cases left
  cases right
  cases reference
  cases forecast
  rfl

theorem node_role_current
    {B : StaticBase} {I : InformationLayer B}
    {R : RepresentationLayer I}
    {F : SelfReferenceFrame R}
    {c d : B.Center}
    (input : ProspectiveFunctionalInput F c d) :
    R.encodedRole input.node = .current := by
  exact F.role_reference c d input.reference

theorem node_stage
    {B : StaticBase} {I : InformationLayer B}
    {R : RepresentationLayer I}
    {F : SelfReferenceFrame R}
    {c d : B.Center}
    (input : ProspectiveFunctionalInput F c d) :
    R.nodeStage input.node = I.actualStage c := by
  exact F.nodeStage_reference c d input.reference

theorem node_perspective
    {B : StaticBase} {I : InformationLayer B}
    {R : RepresentationLayer I}
    {F : SelfReferenceFrame R}
    {c d : B.Center}
    (input : ProspectiveFunctionalInput F c d) :
    R.perspective input.node = some d := by
  exact F.perspective_reference c d input.reference

theorem node_target
    {B : StaticBase} {I : InformationLayer B}
    {R : RepresentationLayer I}
    {F : SelfReferenceFrame R}
    {c d : B.Center}
    (input : ProspectiveFunctionalInput F c d) :
    R.target input.node = some d := by
  exact F.target_reference c d input.reference

/-- Move input data across an annotation-only remoding. -/
def remode
    {B : StaticBase} {I : InformationLayer B}
    {R : RepresentationLayer I}
    {F : SelfReferenceFrame R}
    {c d : B.Center}
    (newMode : R.RepNode → EpistemicMode)
    (input : ProspectiveFunctionalInput F c d) :
    ProspectiveFunctionalInput (F.remode newMode) c d where
  reference := input.reference
  forecast := input.forecast

/-- Pull input data back from an annotation-only remoding. -/
def ofRemode
    {B : StaticBase} {I : InformationLayer B}
    {R : RepresentationLayer I}
    {F : SelfReferenceFrame R}
    {c d : B.Center}
    (newMode : R.RepNode → EpistemicMode)
    (input : ProspectiveFunctionalInput (F.remode newMode) c d) :
    ProspectiveFunctionalInput F c d where
  reference := input.reference
  forecast := input.forecast

theorem remode_ofRemode
    {B : StaticBase} {I : InformationLayer B}
    {R : RepresentationLayer I}
    {F : SelfReferenceFrame R}
    {c d : B.Center}
    (newMode : R.RepNode → EpistemicMode)
    (input : ProspectiveFunctionalInput (F.remode newMode) c d) :
    (input.ofRemode newMode).remode newMode = input := by
  cases input
  rfl

theorem ofRemode_remode
    {B : StaticBase} {I : InformationLayer B}
    {R : RepresentationLayer I}
    {F : SelfReferenceFrame R}
    {c d : B.Center}
    (newMode : R.RepNode → EpistemicMode)
    (input : ProspectiveFunctionalInput F c d) :
    (input.remode newMode).ofRemode newMode = input := by
  cases input
  rfl

theorem remode_injective
    {B : StaticBase} {I : InformationLayer B}
    {R : RepresentationLayer I}
    {F : SelfReferenceFrame R}
    {c d : B.Center}
    (newMode : R.RepNode → EpistemicMode) :
    Function.Injective
      (ProspectiveFunctionalInput.remode (F := F) (c := c) (d := d)
        newMode) := by
  intro left right equal
  have pulled := congrArg
    (ProspectiveFunctionalInput.ofRemode (F := F) (c := c) (d := d)
      newMode) equal
  simpa [ofRemode_remode] using pulled

end ProspectiveFunctionalInput

/-- An input is lawful exactly when its retained forecast has the right
    source/target coordinates and grounds the node realized by its reference. -/
def LawfulProspectiveInput
    {B : StaticBase} {I : InformationLayer B}
    {R : RepresentationLayer I}
    (F : SelfReferenceFrame R)
    (c d : B.Center)
    (input : ProspectiveFunctionalInput F c d) : Prop :=
  ForecastHostedFor I input.forecast c d ∧
  R.groundedByForecast input.node input.forecast

/-- The evidence-bearing, Type-valued stored receipt form of R2.  It contains
    exactly the existing R2 constituents and no downstream-availability or
    functional-use conclusion. -/
structure AvailableProspectiveEncoding
    {B : StaticBase.{uE, uO, uC}}
    {I : InformationLayer.{uE, uO, uC, uS, uR, uF} B}
    {R : RepresentationLayer.{uE, uO, uC, uS, uR, uF, uN} I}
    (F : SelfReferenceFrame.{uA} R)
    (A : CoherentReferenceAction F)
    (c d : B.Center) where
  roleEncoding : InternalRoleEncoding R c d
  continuation : R.continuationCandidate c d
  preservation : PreservesCurrentReference F A c d
  forecast : I.ForecastToken
  hosted : ForecastHostedFor I forecast c d
  grounded :
    R.groundedByForecast
      (F.referenceNode c d
        (A.carry c d (F.currentReference c)))
      forecast

namespace AvailableProspectiveEncoding

def toR2
    {B : StaticBase} {I : InformationLayer B}
    {R : RepresentationLayer I}
    {F : SelfReferenceFrame R}
    {A : CoherentReferenceAction F}
    {c d : B.Center}
    (available : AvailableProspectiveEncoding F A c d) :
    ProspectiveDeSeEncoding F A c d :=
  ⟨available.roleEncoding, available.continuation,
    available.preservation, available.forecast,
    available.hosted, available.grounded⟩

/-- The canonical computational input exposed by stored R2 availability. -/
def input
    {B : StaticBase} {I : InformationLayer B}
    {R : RepresentationLayer I}
    {F : SelfReferenceFrame R}
    {A : CoherentReferenceAction F}
    {c d : B.Center}
    (available : AvailableProspectiveEncoding F A c d) :
    ProspectiveFunctionalInput F c d where
  reference := A.carry c d (F.currentReference c)
  forecast := available.forecast

theorem input_lawful
    {B : StaticBase} {I : InformationLayer B}
    {R : RepresentationLayer I}
    {F : SelfReferenceFrame R}
    {A : CoherentReferenceAction F}
    {c d : B.Center}
    (available : AvailableProspectiveEncoding F A c d) :
    LawfulProspectiveInput F c d available.input := by
  exact ⟨available.hosted, available.grounded⟩

end AvailableProspectiveEncoding

theorem prospective_de_se_iff_available
    {B : StaticBase} {I : InformationLayer B}
    {R : RepresentationLayer I}
    {F : SelfReferenceFrame R}
    {A : CoherentReferenceAction F}
    {c d : B.Center} :
    ProspectiveDeSeEncoding F A c d ↔
      Nonempty (AvailableProspectiveEncoding F A c d) := by
  constructor
  · rintro ⟨r1, continuation, preservation, forecast, hosted, grounded⟩
    exact ⟨{
      roleEncoding := r1
      continuation := continuation
      preservation := preservation
      forecast := forecast
      hosted := hosted
      grounded := grounded
    }⟩
  · rintro ⟨available⟩
    exact available.toR2

/-- A bounded downstream interface.  Presentation may refuse or transform an
    input, but any supplied replacement must retain the exact forecast context
    and must remain lawful.  No field asserts use, relevance, or dependence. -/
structure UptakeLayer
    {B : StaticBase.{uE, uO, uC}}
    {I : InformationLayer.{uE, uO, uC, uS, uR, uF} B}
    {R : RepresentationLayer.{uE, uO, uC, uS, uR, uF, uN} I}
    (F : SelfReferenceFrame.{uA} R)
    (_A : CoherentReferenceAction F) where
  Output : Type uU

  present :
    (c d : B.Center) →
    ProspectiveFunctionalInput F c d →
    Option (ProspectiveFunctionalInput F c d)

  present_erasure :
    ∀ c d input supplied,
      present c d input = some supplied →
      supplied.eraseDeSe = input.eraseDeSe

  present_lawful :
    ∀ c d input supplied,
      LawfulProspectiveInput F c d input →
      present c d input = some supplied →
      LawfulProspectiveInput F c d supplied

  evaluate :
    (c d : B.Center) →
    ProspectiveFunctionalInput F c d → Output

namespace UptakeLayer

/-- The observable result of presentation followed by evaluation. -/
def run
    {B : StaticBase} {I : InformationLayer B}
    {R : RepresentationLayer I}
    {F : SelfReferenceFrame R}
    {A : CoherentReferenceAction F}
    (U : UptakeLayer F A)
    (c d : B.Center)
    (input : ProspectiveFunctionalInput F c d) : Option U.Output :=
  Option.map (U.evaluate c d) (U.present c d input)

/-- Interface availability: some lawful presentation is returned.  This is
    distinct from merely possessing an R2 receipt. -/
def PresentedInputAvailable
    {B : StaticBase} {I : InformationLayer B}
    {R : RepresentationLayer I}
    {F : SelfReferenceFrame R}
    {A : CoherentReferenceAction F}
    (U : UptakeLayer F A)
    (c d : B.Center)
    (input : ProspectiveFunctionalInput F c d) : Prop :=
  ∃ supplied, U.present c d input = some supplied

/-- Faithful consumption: presentation supplies this exact input rather than
    refusing it or substituting a different lawful reference coordinate. -/
def FaithfullyConsumes
    {B : StaticBase} {I : InformationLayer B}
    {R : RepresentationLayer I}
    {F : SelfReferenceFrame R}
    {A : CoherentReferenceAction F}
    (U : UptakeLayer F A)
    (c d : B.Center)
    (input : ProspectiveFunctionalInput F c d) : Prop :=
  U.present c d input = some input

theorem faithfully_consumes_implies_available
    {B : StaticBase} {I : InformationLayer B}
    {R : RepresentationLayer I}
    {F : SelfReferenceFrame R}
    {A : CoherentReferenceAction F}
    (U : UptakeLayer F A)
    {c d : B.Center}
    {input : ProspectiveFunctionalInput F c d}
    (consumes : U.FaithfullyConsumes c d input) :
    U.PresentedInputAvailable c d input :=
  ⟨input, consumes⟩

/-- Lift an uptake layer across annotation-only remoding. -/
def remode
    {B : StaticBase} {I : InformationLayer B}
    {R : RepresentationLayer I}
    {F : SelfReferenceFrame R}
    {A : CoherentReferenceAction F}
    (U : UptakeLayer F A)
    (newMode : R.RepNode → EpistemicMode) :
    UptakeLayer (F.remode newMode) (A.remode newMode) where
  Output := U.Output
  present := fun c d input =>
    Option.map (ProspectiveFunctionalInput.remode newMode)
      (U.present c d (input.ofRemode newMode))
  present_erasure := by
    intro c d input supplied presented
    cases originalEq : U.present c d (input.ofRemode newMode) with
    | none =>
        simp only [originalEq, Option.map] at presented
        cases presented
    | some original =>
        simp only [originalEq, Option.map] at presented
        have suppliedEq : original.remode newMode = supplied :=
          Option.some.inj presented
        cases suppliedEq
        exact U.present_erasure c d (input.ofRemode newMode) original
          originalEq
  present_lawful := by
    intro c d input supplied lawful presented
    cases originalEq : U.present c d (input.ofRemode newMode) with
    | none =>
        simp only [originalEq, Option.map] at presented
        cases presented
    | some original =>
        simp only [originalEq, Option.map] at presented
        have suppliedEq : original.remode newMode = supplied :=
          Option.some.inj presented
        cases suppliedEq
        exact U.present_lawful c d (input.ofRemode newMode) original lawful
          originalEq
  evaluate := fun c d input => U.evaluate c d (input.ofRemode newMode)

theorem present_remode
    {B : StaticBase} {I : InformationLayer B}
    {R : RepresentationLayer I}
    {F : SelfReferenceFrame R}
    {A : CoherentReferenceAction F}
    (U : UptakeLayer.{uU} F A)
    (newMode : R.RepNode → EpistemicMode)
    {c d : B.Center}
    (input supplied : ProspectiveFunctionalInput F c d) :
    (U.remode newMode).present c d (input.remode newMode) =
        some (supplied.remode newMode) ↔
      U.present c d input = some supplied := by
  constructor
  · intro presented
    change Option.map
        (ProspectiveFunctionalInput.remode
          (F := F) (c := c) (d := d) newMode)
        (U.present c d ((input.remode newMode).ofRemode newMode)) =
      some (supplied.remode newMode) at presented
    rw [ProspectiveFunctionalInput.ofRemode_remode] at presented
    cases originalEq : U.present c d input with
    | none =>
        rw [originalEq] at presented
        cases presented
    | some original =>
        rw [originalEq] at presented
        have someMapped :
            some (original.remode newMode) =
              some (supplied.remode newMode) := by
          exact presented
        have mapped : original.remode newMode = supplied.remode newMode := by
          exact Option.some.inj someMapped
        have originalEqSupplied :=
          ProspectiveFunctionalInput.remode_injective
            (F := F) (c := c) (d := d) newMode mapped
        exact congrArg some originalEqSupplied
  · intro presented
    change Option.map
        (ProspectiveFunctionalInput.remode
          (F := F) (c := c) (d := d) newMode)
        (U.present c d ((input.remode newMode).ofRemode newMode)) =
      some (supplied.remode newMode)
    rw [ProspectiveFunctionalInput.ofRemode_remode, presented]
    rfl

theorem evaluate_remode
    {B : StaticBase} {I : InformationLayer B}
    {R : RepresentationLayer I}
    {F : SelfReferenceFrame R}
    {A : CoherentReferenceAction F}
    (U : UptakeLayer.{uU} F A)
    (newMode : R.RepNode → EpistemicMode)
    {c d : B.Center}
    (input : ProspectiveFunctionalInput F c d) :
    (U.remode newMode).evaluate c d (input.remode newMode) =
      U.evaluate c d input := by
  rfl

theorem lawful_input_remode
    {B : StaticBase} {I : InformationLayer B}
    {R : RepresentationLayer I}
    {F : SelfReferenceFrame R}
    (newMode : R.RepNode → EpistemicMode)
    {c d : B.Center}
    (input : ProspectiveFunctionalInput F c d) :
    LawfulProspectiveInput (F.remode newMode) c d
        (input.remode newMode) ↔
      LawfulProspectiveInput F c d input := by
  rfl

end UptakeLayer

end StaticRole
