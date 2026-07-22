/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE
-/

import StaticRole.Model.UptakeIsomorphism
import StaticRole.Functional.Dependence

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
  {U1 : UptakeLayer.{uE1, uO1, uC1, uS1, uR1, uF1, uN1, uA1, uU1}
    F1 A1}
  {B2 : StaticBase.{uE2, uO2, uC2}}
  {I2 : InformationLayer.{uE2, uO2, uC2, uS2, uR2, uF2} B2}
  {R2 : RepresentationLayer.{uE2, uO2, uC2, uS2, uR2, uF2, uN2} I2}
  {F2 : SelfReferenceFrame.{uA2} R2}
  {A2 : CoherentReferenceAction F2}
  {U2 : UptakeLayer.{uE2, uO2, uC2, uS2, uR2, uF2, uN2, uA2, uU2}
    F2 A2}

/-- Functional uptake is preserved and reflected by a full signature
    isomorphism extended only with the functional output and operation laws. -/
theorem functional_uptake_transport
    (iso : FullSignatureIso (F1 := F1) (A1 := A1) (F2 := F2) (A2 := A2))
    (uptakeIso : UptakeLayerIso iso U1 U2)
    (c d : B1.Center) :
    FunctionalUptake F1 A1 U1 c d ↔
      FunctionalUptake F2 A2 U2
        (iso.centerIso.toFun c) (iso.centerIso.toFun d) := by
  let inputIso := prospectiveFunctionalInputIso iso c d
  constructor
  · rintro ⟨r2, actual, alternate, actualLawful, alternateLawful,
      actualReference, sameErasure, referencesDiffer,
      actualPresented, alternatePresented, outputsDiffer⟩
    refine ⟨(prospective_de_se_encoding_transport iso c d).mp r2,
      inputIso.toFun actual, inputIso.toFun alternate,
      (lawful_prospective_input_transport iso c d actual).mp actualLawful,
      (lawful_prospective_input_transport iso c d alternate).mp alternateLawful,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · change iso.referenceIso.toFun actual.reference =
        A2.carry (iso.centerIso.toFun c) (iso.centerIso.toFun d)
          (F2.currentReference (iso.centerIso.toFun c))
      calc
        iso.referenceIso.toFun actual.reference =
            iso.referenceIso.toFun
              (A1.carry c d (F1.currentReference c)) :=
          congrArg iso.referenceIso.toFun actualReference
        _ = A2.carry (iso.centerIso.toFun c) (iso.centerIso.toFun d)
            (iso.referenceIso.toFun (F1.currentReference c)) :=
          iso.carry_preserved c d (F1.currentReference c)
        _ = A2.carry (iso.centerIso.toFun c) (iso.centerIso.toFun d)
            (F2.currentReference (iso.centerIso.toFun c)) :=
          congrArg (A2.carry (iso.centerIso.toFun c)
            (iso.centerIso.toFun d)) (iso.currentReference_preserved c)
    · exact congrArg iso.forecastIso.toFun sameErasure
    · intro mappedEqual
      exact referencesDiffer (iso.referenceIso.injective mappedEqual)
    · exact (uptakeIso.present_self_transport c d actual).mp actualPresented
    · exact (uptakeIso.present_self_transport c d alternate).mp
        alternatePresented
    · intro mappedOutputsEqual
      apply outputsDiffer
      apply uptakeIso.outputIso.injective
      calc
        uptakeIso.outputIso.toFun (U1.evaluate c d actual) =
            U2.evaluate (iso.centerIso.toFun c) (iso.centerIso.toFun d)
              (inputIso.toFun actual) :=
          uptakeIso.evaluate_preserved c d actual
        _ = U2.evaluate (iso.centerIso.toFun c) (iso.centerIso.toFun d)
              (inputIso.toFun alternate) := mappedOutputsEqual
        _ = uptakeIso.outputIso.toFun (U1.evaluate c d alternate) :=
          (uptakeIso.evaluate_preserved c d alternate).symm
  · rintro ⟨r2, targetActual, targetAlternate,
      targetActualLawful, targetAlternateLawful,
      targetActualReference, targetSameErasure, targetReferencesDiffer,
      targetActualPresented, targetAlternatePresented, targetOutputsDiffer⟩
    let actual := inputIso.invFun targetActual
    let alternate := inputIso.invFun targetAlternate
    have actualRoundTrip : inputIso.toFun actual = targetActual :=
      inputIso.right_inv targetActual
    have alternateRoundTrip : inputIso.toFun alternate = targetAlternate :=
      inputIso.right_inv targetAlternate
    refine ⟨(prospective_de_se_encoding_transport iso c d).mpr r2,
      actual, alternate, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · apply (lawful_prospective_input_transport iso c d actual).mpr
      rw [actualRoundTrip]
      exact targetActualLawful
    · apply (lawful_prospective_input_transport iso c d alternate).mpr
      rw [alternateRoundTrip]
      exact targetAlternateLawful
    · apply iso.referenceIso.injective
      calc
        iso.referenceIso.toFun actual.reference = targetActual.reference :=
          congrArg ProspectiveFunctionalInput.reference actualRoundTrip
        _ = A2.carry (iso.centerIso.toFun c) (iso.centerIso.toFun d)
            (F2.currentReference (iso.centerIso.toFun c)) :=
          targetActualReference
        _ = A2.carry (iso.centerIso.toFun c) (iso.centerIso.toFun d)
            (iso.referenceIso.toFun (F1.currentReference c)) :=
          congrArg (A2.carry (iso.centerIso.toFun c)
            (iso.centerIso.toFun d)) (iso.currentReference_preserved c).symm
        _ = iso.referenceIso.toFun
            (A1.carry c d (F1.currentReference c)) :=
          (iso.carry_preserved c d (F1.currentReference c)).symm
    · apply iso.forecastIso.injective
      calc
        iso.forecastIso.toFun actual.eraseDeSe = targetActual.eraseDeSe :=
          congrArg ProspectiveFunctionalInput.eraseDeSe actualRoundTrip
        _ = targetAlternate.eraseDeSe := targetSameErasure
        _ = iso.forecastIso.toFun alternate.eraseDeSe :=
          (congrArg ProspectiveFunctionalInput.eraseDeSe
            alternateRoundTrip).symm
    · intro sourceReferencesEqual
      apply targetReferencesDiffer
      calc
        targetActual.reference = iso.referenceIso.toFun actual.reference :=
          (congrArg ProspectiveFunctionalInput.reference actualRoundTrip).symm
        _ = iso.referenceIso.toFun alternate.reference :=
          congrArg iso.referenceIso.toFun sourceReferencesEqual
        _ = targetAlternate.reference :=
          congrArg ProspectiveFunctionalInput.reference alternateRoundTrip
    · apply (uptakeIso.present_self_transport c d actual).mpr
      rw [actualRoundTrip]
      exact targetActualPresented
    · apply (uptakeIso.present_self_transport c d alternate).mpr
      rw [alternateRoundTrip]
      exact targetAlternatePresented
    · intro sourceOutputsEqual
      apply targetOutputsDiffer
      calc
        U2.evaluate (iso.centerIso.toFun c) (iso.centerIso.toFun d)
            targetActual =
          U2.evaluate (iso.centerIso.toFun c) (iso.centerIso.toFun d)
            (inputIso.toFun actual) :=
          congrArg (U2.evaluate (iso.centerIso.toFun c)
            (iso.centerIso.toFun d)) actualRoundTrip.symm
        _ = uptakeIso.outputIso.toFun (U1.evaluate c d actual) :=
          (uptakeIso.evaluate_preserved c d actual).symm
        _ = uptakeIso.outputIso.toFun (U1.evaluate c d alternate) :=
          congrArg uptakeIso.outputIso.toFun sourceOutputsEqual
        _ = U2.evaluate (iso.centerIso.toFun c) (iso.centerIso.toFun d)
            (inputIso.toFun alternate) :=
          uptakeIso.evaluate_preserved c d alternate
        _ = U2.evaluate (iso.centerIso.toFun c) (iso.centerIso.toFun d)
            targetAlternate :=
          congrArg (U2.evaluate (iso.centerIso.toFun c)
            (iso.centerIso.toFun d)) alternateRoundTrip

/-- The richer concrete functional witness transports in both directions as
    a consequence of the substantive characterization and R3 transport. -/
theorem coherent_functional_uptake_witness_transport
    (iso : FullSignatureIso (F1 := F1) (A1 := A1) (F2 := F2) (A2 := A2))
    (uptakeIso : UptakeLayerIso iso U1 U2)
    (c d : B1.Center) :
    Nonempty (CoherentFunctionalUptakeWitness F1 A1 U1 c d) ↔
      Nonempty (CoherentFunctionalUptakeWitness F2 A2 U2
        (iso.centerIso.toFun c) (iso.centerIso.toFun d)) := by
  calc
    Nonempty (CoherentFunctionalUptakeWitness F1 A1 U1 c d) ↔
        FunctionalUptake F1 A1 U1 c d :=
      functional_uptake_iff_nontrivial_de_se_dependence.symm
    _ ↔ FunctionalUptake F2 A2 U2
          (iso.centerIso.toFun c) (iso.centerIso.toFun d) :=
      functional_uptake_transport iso uptakeIso c d
    _ ↔ Nonempty (CoherentFunctionalUptakeWitness F2 A2 U2
          (iso.centerIso.toFun c) (iso.centerIso.toFun d)) :=
      functional_uptake_iff_nontrivial_de_se_dependence

end StaticRole
