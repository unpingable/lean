/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE
-/

import StaticRole.Countermodels.UptakeHostiles

namespace StaticRole.Theorems.UptakeIndependence

open Countermodels.CoherenceHostiles
open Countermodels.UptakeHostiles

/-- The hierarchy's positive direction: functional uptake contains, rather
    than reconstructs or replaces, the bounded R2 judgment. -/
theorem r3_implies_r2
    {B : StaticBase} {I : InformationLayer B}
    {R : RepresentationLayer I}
    {F : SelfReferenceFrame R}
    {A : CoherentReferenceAction F}
    {U : UptakeLayer F A}
    {c d : B.Center}
    (r3 : FunctionalUptake F A U c d) :
    ProspectiveDeSeEncoding F A c d :=
  functional_uptake_implies_r2 r3

/-- R2 is insufficient even when its exact stored receipt is available and a
    lawful downstream layer exists. -/
theorem exists_r2_not_r3 :
    ProspectiveDeSeEncoding coherenceFrame parityAction false true ∧
    ¬ FunctionalUptake coherenceFrame parityAction neutralizingUptake
      false true :=
  r2_without_uptake

/-- R1 cannot skip the coherence-grounded R2 bridge and acquire R3 directly. -/
theorem exists_r1_not_r3 :
    InternalRoleEncoding coherenceRepresentation false true ∧
    ¬ FunctionalUptake coherenceFrame fixedAction fixedConstantUptake
      false true :=
  r1_without_uptake

/-- Availability and actual faithful consumption remain distinct judgments. -/
theorem available_input_without_consumption :
    neutralizingUptake.PresentedInputAvailable false true actualInput ∧
    ¬ neutralizingUptake.FaithfullyConsumes false true actualInput ∧
    ¬ FunctionalUptake coherenceFrame parityAction neutralizingUptake
      false true :=
  presented_availability_without_faithful_consumption

/-- Projecting the forecast is a real computation on the supplied input, but
    it factors through de se erasure and is therefore not R3. -/
theorem consumes_forecast_not_de_se :
    forecastOnlyUptake.FaithfullyConsumes false true actualInput ∧
    FactorsThroughDeSeErasure forecastOnlyUptake false true ∧
    ¬ FunctionalUptake coherenceFrame parityAction forecastOnlyUptake
      false true :=
  faithful_forecast_consumption_still_not_de_se_uptake

/-- A reference-sensitive transition may be functionally active while wrong
    under an independently supplied correctness predicate. -/
theorem r3_without_output_correctness :
    FunctionalUptake coherenceFrame parityAction faithfulUptake false true ∧
    faithfulUptake.run false true coherenceAvailable.input = some true ∧
    ¬ OutputCorrect true :=
  de_se_dependence_without_success

/-- Conversely, an accidentally correct constant result has no uptake force. -/
theorem output_correctness_without_r3 :
    constantUptake.run false true coherenceAvailable.input = some false ∧
    OutputCorrect false ∧
    ¬ FunctionalUptake coherenceFrame parityAction constantUptake false true :=
  successful_output_without_uptake

/-- Valid mnemonic provenance remains insufficient for R3. -/
theorem mnemonic_records_do_not_establish_r3 :
    MemoryAttributed mnemonicCoherenceRepresentation (.atlas true false) ∧
    mnemonicCoherenceInformation.traceValid PUnit.unit ∧
    ¬ FunctionalUptake mnemonicCoherenceFrame mnemonicFixedAction
      mnemonicConstantUptake false true :=
  mnemonic_records_without_uptake

/-- Continuation alone remains below both R2 and R3. -/
theorem continuation_does_not_establish_r3 :
    coherenceRepresentation.continuationCandidate false true ∧
    ¬ FunctionalUptake coherenceFrame fixedAction fixedConstantUptake
      false true :=
  continuation_without_uptake

/-- Forecast grounding alone also remains insufficient. -/
theorem forecast_grounding_does_not_establish_r3 :
    coherenceRepresentation.groundedByForecast
      (.reference false true true) PUnit.unit ∧
    ¬ FunctionalUptake coherenceFrame parityAction constantUptake false true :=
  forecast_grounding_without_uptake

/-- The critical same-reduct theorem changes only the lawful presentation map
    while retaining one literal R2 receipt and evaluator. -/
theorem same_r2_reduct_different_functional_uptake :
    FunctionalUptake coherenceFrame parityAction faithfulUptake false true ∧
    ¬ FunctionalUptake coherenceFrame parityAction neutralizingUptake
      false true :=
  same_r2_and_evaluator_presentations_disagree_on_r3

/-- Two actual R2 inputs in one shared finite frame can drive distinct results. -/
theorem shared_frame_r2_inputs_can_discriminate :
    FunctionalUptake threeFrame threeAction threeFaithfulUptake
        .source .left ∧
    FunctionalUptake threeFrame threeAction threeFaithfulUptake
        .source .right ∧
    threeFaithfulUptake.run .source .left leftAvailable.input = some false ∧
    threeFaithfulUptake.run .source .right rightAvailable.input = some true :=
  two_r2_inputs_each_have_r3_and_distinct_results

/-- Possessing different lawful R2 contents does not force downstream
    discrimination: the same shared frame admits a constant transition. -/
theorem shared_frame_r2_inputs_need_not_discriminate :
    ProspectiveDeSeEncoding threeFrame threeAction .source .left ∧
    ProspectiveDeSeEncoding threeFrame threeAction .source .right ∧
    threeConstantUptake.run .source .left leftAvailable.input =
      threeConstantUptake.run .source .right rightAvailable.input ∧
    ¬ FunctionalUptake threeFrame threeAction threeConstantUptake
        .source .left ∧
    ¬ FunctionalUptake threeFrame threeAction threeConstantUptake
        .source .right :=
  distinct_r2_inputs_same_output_without_r3

end StaticRole.Theorems.UptakeIndependence
