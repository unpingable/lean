/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE
-/

import StaticRole.Model.Transport
import StaticRole.Functional.Uptake

namespace StaticRole

universe
  uE1 uO1 uC1 uS1 uR1 uF1 uN1 uA1 uU1
  uE2 uO2 uC2 uS2 uR2 uF2 uN2 uA2 uU2

variable
  {B1 : StaticBase.{uE1, uO1, uC1}}
  {I1 : InformationLayer.{uE1, uO1, uC1, uS1, uR1, uF1} B1}
  {R1 : RepresentationLayer.{uE1, uO1, uC1, uS1, uR1, uF1, uN1} I1}
  {F1 : SelfReferenceFrame.{uA1} R1}
  {A1 : CoherentReferenceAction F1}
  {B2 : StaticBase.{uE2, uO2, uC2}}
  {I2 : InformationLayer.{uE2, uO2, uC2, uS2, uR2, uF2} B2}
  {R2 : RepresentationLayer.{uE2, uO2, uC2, uS2, uR2, uF2, uN2} I2}
  {F2 : SelfReferenceFrame.{uA2} R2}
  {A2 : CoherentReferenceAction F2}

/-- The functional-input fibers are transported by the already-ratified
    reference and forecast isomorphisms.  No new input carrier is postulated. -/
def prospectiveFunctionalInputIso
    (iso : FullSignatureIso (F1 := F1) (A1 := A1) (F2 := F2) (A2 := A2))
    (c d : B1.Center) :
    SortIso (ProspectiveFunctionalInput F1 c d)
      (ProspectiveFunctionalInput F2
        (iso.centerIso.toFun c) (iso.centerIso.toFun d)) where
  toFun := fun input => {
    reference := iso.referenceIso.toFun input.reference
    forecast := iso.forecastIso.toFun input.forecast
  }
  invFun := fun input => {
    reference := iso.referenceIso.invFun input.reference
    forecast := iso.forecastIso.invFun input.forecast
  }
  left_inv := by
    intro input
    apply ProspectiveFunctionalInput.ext
    · exact iso.referenceIso.left_inv input.reference
    · exact iso.forecastIso.left_inv input.forecast
  right_inv := by
    intro input
    apply ProspectiveFunctionalInput.ext
    · exact iso.referenceIso.right_inv input.reference
    · exact iso.forecastIso.right_inv input.forecast

theorem prospective_functional_input_node_preserved
    (iso : FullSignatureIso (F1 := F1) (A1 := A1) (F2 := F2) (A2 := A2))
    (c d : B1.Center) (input : ProspectiveFunctionalInput F1 c d) :
    iso.nodeIso.toFun input.node =
      ((prospectiveFunctionalInputIso iso c d).toFun input).node := by
  exact iso.referenceNode_preserved c d input.reference

theorem prospective_functional_input_erasure_preserved
    (iso : FullSignatureIso (F1 := F1) (A1 := A1) (F2 := F2) (A2 := A2))
    (c d : B1.Center) (input : ProspectiveFunctionalInput F1 c d) :
    iso.forecastIso.toFun input.eraseDeSe =
      ((prospectiveFunctionalInputIso iso c d).toFun input).eraseDeSe := by
  rfl

/-- Lawfulness of an input is preserved and reflected by the derived input
    isomorphism. -/
theorem lawful_prospective_input_transport
    (iso : FullSignatureIso (F1 := F1) (A1 := A1) (F2 := F2) (A2 := A2))
    (c d : B1.Center) (input : ProspectiveFunctionalInput F1 c d) :
    LawfulProspectiveInput F1 c d input ↔
      LawfulProspectiveInput F2 (iso.centerIso.toFun c)
        (iso.centerIso.toFun d)
        ((prospectiveFunctionalInputIso iso c d).toFun input) := by
  constructor
  · rintro ⟨hosted, grounded⟩
    refine ⟨(forecast_hosted_for_transport iso input.forecast c d).mp hosted, ?_⟩
    have transported :=
      (iso.groundedByForecast_iff input.node input.forecast).mp grounded
    rw [prospective_functional_input_node_preserved iso c d input] at transported
    exact transported
  · rintro ⟨hosted, grounded⟩
    refine ⟨(forecast_hosted_for_transport iso input.forecast c d).mpr hosted, ?_⟩
    apply (iso.groundedByForecast_iff input.node input.forecast).mpr
    rw [prospective_functional_input_node_preserved iso c d input]
    exact grounded

/-- Public phase-three form of the carried-node preservation calculation.
    The analogous phase-two helper is deliberately private. -/
theorem carried_functional_node_preserved
    (iso : FullSignatureIso (F1 := F1) (A1 := A1) (F2 := F2) (A2 := A2))
    (c d : B1.Center) :
    iso.nodeIso.toFun
        (F1.referenceNode c d
          (A1.carry c d (F1.currentReference c))) =
      F2.referenceNode (iso.centerIso.toFun c) (iso.centerIso.toFun d)
        (A2.carry (iso.centerIso.toFun c) (iso.centerIso.toFun d)
          (F2.currentReference (iso.centerIso.toFun c))) := by
  calc
    iso.nodeIso.toFun
        (F1.referenceNode c d
          (A1.carry c d (F1.currentReference c))) =
      F2.referenceNode (iso.centerIso.toFun c) (iso.centerIso.toFun d)
        (iso.referenceIso.toFun
          (A1.carry c d (F1.currentReference c))) :=
      iso.referenceNode_preserved c d
        (A1.carry c d (F1.currentReference c))
    _ = F2.referenceNode (iso.centerIso.toFun c) (iso.centerIso.toFun d)
        (A2.carry (iso.centerIso.toFun c) (iso.centerIso.toFun d)
          (iso.referenceIso.toFun (F1.currentReference c))) :=
      congrArg (F2.referenceNode (iso.centerIso.toFun c)
        (iso.centerIso.toFun d))
        (iso.carry_preserved c d (F1.currentReference c))
    _ = F2.referenceNode (iso.centerIso.toFun c) (iso.centerIso.toFun d)
        (A2.carry (iso.centerIso.toFun c) (iso.centerIso.toFun d)
          (F2.currentReference (iso.centerIso.toFun c))) :=
      congrArg (fun reference =>
        F2.referenceNode (iso.centerIso.toFun c) (iso.centerIso.toFun d)
          (A2.carry (iso.centerIso.toFun c) (iso.centerIso.toFun d) reference))
        (iso.currentReference_preserved c)

/-- Constructively map stored R2 availability into the target signature. -/
def AvailableProspectiveEncoding.map
    (iso : FullSignatureIso (F1 := F1) (A1 := A1) (F2 := F2) (A2 := A2))
    {c d : B1.Center}
    (available : AvailableProspectiveEncoding F1 A1 c d) :
    AvailableProspectiveEncoding F2 A2
      (iso.centerIso.toFun c) (iso.centerIso.toFun d) where
  roleEncoding :=
    (internal_role_encoding_transport iso c d).mp available.roleEncoding
  continuation :=
    (iso.continuationCandidate_iff c d).mp available.continuation
  preservation :=
    (preserves_current_reference_transport iso c d).mp available.preservation
  forecast := iso.forecastIso.toFun available.forecast
  hosted :=
    (forecast_hosted_for_transport iso available.forecast c d).mp
      available.hosted
  grounded := by
    have transported :=
      (iso.groundedByForecast_iff
        (F1.referenceNode c d
          (A1.carry c d (F1.currentReference c)))
        available.forecast).mp available.grounded
    rw [carried_functional_node_preserved iso c d] at transported
    exact transported

/-- Constructively pull stored availability back from the mapped target
    fiber.  This uses the explicit inverses already present in `SortIso`. -/
def AvailableProspectiveEncoding.pullback
    (iso : FullSignatureIso (F1 := F1) (A1 := A1) (F2 := F2) (A2 := A2))
    {c d : B1.Center}
    (available : AvailableProspectiveEncoding F2 A2
      (iso.centerIso.toFun c) (iso.centerIso.toFun d)) :
    AvailableProspectiveEncoding F1 A1 c d where
  roleEncoding :=
    (internal_role_encoding_transport iso c d).mpr available.roleEncoding
  continuation :=
    (iso.continuationCandidate_iff c d).mpr available.continuation
  preservation :=
    (preserves_current_reference_transport iso c d).mpr available.preservation
  forecast := iso.forecastIso.invFun available.forecast
  hosted := by
    apply (forecast_hosted_for_transport iso
      (iso.forecastIso.invFun available.forecast) c d).mpr
    rw [iso.forecastIso.right_inv]
    exact available.hosted
  grounded := by
    apply (iso.groundedByForecast_iff
      (F1.referenceNode c d
        (A1.carry c d (F1.currentReference c)))
      (iso.forecastIso.invFun available.forecast)).mpr
    rw [carried_functional_node_preserved iso c d,
      iso.forecastIso.right_inv]
    exact available.grounded

theorem available_input_preserved
    (iso : FullSignatureIso (F1 := F1) (A1 := A1) (F2 := F2) (A2 := A2))
    {c d : B1.Center}
    (available : AvailableProspectiveEncoding F1 A1 c d) :
    (prospectiveFunctionalInputIso iso c d).toFun available.input =
      (available.map iso).input := by
  apply ProspectiveFunctionalInput.ext
  · change iso.referenceIso.toFun
        (A1.carry c d (F1.currentReference c)) =
      A2.carry (iso.centerIso.toFun c) (iso.centerIso.toFun d)
        (F2.currentReference (iso.centerIso.toFun c))
    calc
      iso.referenceIso.toFun
          (A1.carry c d (F1.currentReference c)) =
        A2.carry (iso.centerIso.toFun c) (iso.centerIso.toFun d)
          (iso.referenceIso.toFun (F1.currentReference c)) :=
        iso.carry_preserved c d (F1.currentReference c)
      _ = A2.carry (iso.centerIso.toFun c) (iso.centerIso.toFun d)
          (F2.currentReference (iso.centerIso.toFun c)) :=
        congrArg (A2.carry (iso.centerIso.toFun c)
          (iso.centerIso.toFun d)) (iso.currentReference_preserved c)
  · rfl

theorem pullback_available_input_roundtrip
    (iso : FullSignatureIso (F1 := F1) (A1 := A1) (F2 := F2) (A2 := A2))
    {c d : B1.Center}
    (available : AvailableProspectiveEncoding F2 A2
      (iso.centerIso.toFun c) (iso.centerIso.toFun d)) :
    (prospectiveFunctionalInputIso iso c d).toFun
        (available.pullback iso).input = available.input := by
  apply ProspectiveFunctionalInput.ext
  · change iso.referenceIso.toFun
        (A1.carry c d (F1.currentReference c)) =
      A2.carry (iso.centerIso.toFun c) (iso.centerIso.toFun d)
        (F2.currentReference (iso.centerIso.toFun c))
    calc
      iso.referenceIso.toFun
          (A1.carry c d (F1.currentReference c)) =
        A2.carry (iso.centerIso.toFun c) (iso.centerIso.toFun d)
          (iso.referenceIso.toFun (F1.currentReference c)) :=
        iso.carry_preserved c d (F1.currentReference c)
      _ = A2.carry (iso.centerIso.toFun c) (iso.centerIso.toFun d)
          (F2.currentReference (iso.centerIso.toFun c)) :=
        congrArg (A2.carry (iso.centerIso.toFun c)
          (iso.centerIso.toFun d)) (iso.currentReference_preserved c)
  · exact iso.forecastIso.right_inv available.forecast

/-- A phase-three extension of the frozen full-signature isomorphism.  Its
    only additional data are an output isomorphism and commutation of the two
    functional operations with the derived input isomorphism. -/
structure UptakeLayerIso
    (iso : FullSignatureIso (F1 := F1) (A1 := A1) (F2 := F2) (A2 := A2))
    (U1 : UptakeLayer.{uE1, uO1, uC1, uS1, uR1, uF1, uN1, uA1, uU1}
      F1 A1)
    (U2 : UptakeLayer.{uE2, uO2, uC2, uS2, uR2, uF2, uN2, uA2, uU2}
      F2 A2) where
  outputIso : SortIso U1.Output U2.Output

  present_preserved :
    ∀ c d input,
      Option.map (prospectiveFunctionalInputIso iso c d).toFun
          (U1.present c d input) =
        U2.present (iso.centerIso.toFun c) (iso.centerIso.toFun d)
          ((prospectiveFunctionalInputIso iso c d).toFun input)

  evaluate_preserved :
    ∀ c d input,
      outputIso.toFun (U1.evaluate c d input) =
        U2.evaluate (iso.centerIso.toFun c) (iso.centerIso.toFun d)
          ((prospectiveFunctionalInputIso iso c d).toFun input)

namespace UptakeLayerIso

theorem present_self_transport
    {iso : FullSignatureIso (F1 := F1) (A1 := A1) (F2 := F2) (A2 := A2)}
    {U1 : UptakeLayer.{uE1, uO1, uC1, uS1, uR1, uF1, uN1, uA1, uU1}
      F1 A1}
    {U2 : UptakeLayer.{uE2, uO2, uC2, uS2, uR2, uF2, uN2, uA2, uU2}
      F2 A2}
    (uptakeIso : UptakeLayerIso iso U1 U2)
    (c d : B1.Center) (input : ProspectiveFunctionalInput F1 c d) :
    U1.present c d input = some input ↔
      U2.present (iso.centerIso.toFun c) (iso.centerIso.toFun d)
        ((prospectiveFunctionalInputIso iso c d).toFun input) =
          some ((prospectiveFunctionalInputIso iso c d).toFun input) := by
  constructor
  · intro presented
    rw [← uptakeIso.present_preserved c d input, presented]
    rfl
  · intro presented
    have mappedPresentation := uptakeIso.present_preserved c d input
    rw [presented] at mappedPresentation
    generalize sourceEq : U1.present c d input = source at mappedPresentation
    cases source with
    | none => cases mappedPresentation
    | some supplied =>
        have mappedEqual :
            (prospectiveFunctionalInputIso iso c d).toFun supplied =
              (prospectiveFunctionalInputIso iso c d).toFun input :=
          Option.some.inj mappedPresentation
        have suppliedEqual :=
          (prospectiveFunctionalInputIso iso c d).injective mappedEqual
        exact congrArg some suppliedEqual

end UptakeLayerIso

end StaticRole
