/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE
-/

import StaticRole.Functional.Uptake

namespace StaticRole

universe uU

/-- R3: exact R2 possession plus faithful presentation of two lawful inputs
    which share all retained forecast context, differ in the transported
    reference coordinate, and produce different downstream results. -/
def FunctionalUptake
    {B : StaticBase} {I : InformationLayer B}
    {R : RepresentationLayer I}
    (F : SelfReferenceFrame R)
    (A : CoherentReferenceAction F)
    (U : UptakeLayer.{uU} F A)
    (c d : B.Center) : Prop :=
  ProspectiveDeSeEncoding F A c d ∧
  ∃ actual alternate : ProspectiveFunctionalInput F c d,
    LawfulProspectiveInput F c d actual ∧
    LawfulProspectiveInput F c d alternate ∧
    actual.reference = A.carry c d (F.currentReference c) ∧
    actual.eraseDeSe = alternate.eraseDeSe ∧
    actual.reference ≠ alternate.reference ∧
    U.present c d actual = some actual ∧
    U.present c d alternate = some alternate ∧
    U.evaluate c d actual ≠ U.evaluate c d alternate

/-- A concrete node-level receipt for functional dependence.  It stores
    actual transition observations, not an asserted relevance predicate. -/
structure CoherentFunctionalUptakeWitness
    {B : StaticBase} {I : InformationLayer B}
    {R : RepresentationLayer I}
    (F : SelfReferenceFrame R)
    (A : CoherentReferenceAction F)
    (U : UptakeLayer.{uU} F A)
    (c d : B.Center) where
  available : AvailableProspectiveEncoding F A c d

  actual : ProspectiveFunctionalInput F c d
  alternate : ProspectiveFunctionalInput F c d
  suppliedActual : ProspectiveFunctionalInput F c d
  suppliedAlternate : ProspectiveFunctionalInput F c d

  actualLawful : LawfulProspectiveInput F c d actual
  alternateLawful : LawfulProspectiveInput F c d alternate
  actualForecast : actual.forecast = available.forecast
  sameErasure : actual.eraseDeSe = alternate.eraseDeSe

  actualEndpoint :
    actual.node =
      F.referenceNode c d (A.carry c d (F.currentReference c))
  nodesDiffer : actual.node ≠ alternate.node

  actualPresented : U.present c d actual = some suppliedActual
  alternatePresented : U.present c d alternate = some suppliedAlternate
  actualPresentationErasure :
    suppliedActual.eraseDeSe = actual.eraseDeSe
  alternatePresentationErasure :
    suppliedAlternate.eraseDeSe = alternate.eraseDeSe
  actualPresentationNode : suppliedActual.node = actual.node
  alternatePresentationNode : suppliedAlternate.node = alternate.node

  outputsDiffer :
    U.evaluate c d suppliedActual ≠ U.evaluate c d suppliedAlternate

private theorem supplied_input_eq
    {B : StaticBase} {I : InformationLayer B}
    {R : RepresentationLayer I}
    {F : SelfReferenceFrame R}
    {c d : B.Center}
    {source supplied : ProspectiveFunctionalInput F c d}
    (node : supplied.node = source.node)
    (erasure : supplied.eraseDeSe = source.eraseDeSe) :
    supplied = source := by
  apply ProspectiveFunctionalInput.ext
  · exact F.referenceNode_injective c d node
  · exact erasure

/-- The surface R3 predicate is equivalent to a concrete node-level
    dependence receipt.  Injectivity of reference realization is required to
    recover faithful presentation and the canonical transported coordinate. -/
theorem functional_uptake_iff_nontrivial_de_se_dependence
    {B : StaticBase} {I : InformationLayer B}
    {R : RepresentationLayer I}
    {F : SelfReferenceFrame R}
    {A : CoherentReferenceAction F}
    {U : UptakeLayer.{uU} F A}
    {c d : B.Center} :
    FunctionalUptake F A U c d ↔
      Nonempty (CoherentFunctionalUptakeWitness F A U c d) := by
  constructor
  · rintro ⟨r2, actual, alternate, actualLawful, alternateLawful,
      actualReference, sameErasure, referencesDiffer,
      actualPresented, alternatePresented, outputsDiffer⟩
    let available : AvailableProspectiveEncoding F A c d := {
      roleEncoding := r2.1
      continuation := r2.2.1
      preservation := r2.2.2.1
      forecast := actual.forecast
      hosted := actualLawful.1
      grounded := by
        rw [← actualReference]
        exact actualLawful.2
    }
    refine ⟨{
      available := available
      actual := actual
      alternate := alternate
      suppliedActual := actual
      suppliedAlternate := alternate
      actualLawful := actualLawful
      alternateLawful := alternateLawful
      actualForecast := rfl
      sameErasure := sameErasure
      actualEndpoint := ?_
      nodesDiffer := ?_
      actualPresented := actualPresented
      alternatePresented := alternatePresented
      actualPresentationErasure := rfl
      alternatePresentationErasure := rfl
      actualPresentationNode := rfl
      alternatePresentationNode := rfl
      outputsDiffer := outputsDiffer
    }⟩
    · exact congrArg (F.referenceNode c d) actualReference
    · intro nodeEquality
      exact referencesDiffer (F.referenceNode_injective c d nodeEquality)
  · rintro ⟨witness⟩
    have actualReference :
        witness.actual.reference =
          A.carry c d (F.currentReference c) :=
      F.referenceNode_injective c d witness.actualEndpoint
    have referencesDiffer :
        witness.actual.reference ≠ witness.alternate.reference := by
      intro referencesEqual
      apply witness.nodesDiffer
      exact congrArg (F.referenceNode c d) referencesEqual
    have suppliedActualEq : witness.suppliedActual = witness.actual :=
      supplied_input_eq witness.actualPresentationNode
        witness.actualPresentationErasure
    have suppliedAlternateEq :
        witness.suppliedAlternate = witness.alternate :=
      supplied_input_eq witness.alternatePresentationNode
        witness.alternatePresentationErasure
    refine ⟨witness.available.toR2, witness.actual, witness.alternate,
      witness.actualLawful, witness.alternateLawful, actualReference,
      witness.sameErasure, referencesDiffer, ?_, ?_, ?_⟩
    · simpa [suppliedActualEq] using witness.actualPresented
    · simpa [suppliedAlternateEq] using witness.alternatePresented
    · intro outputsEqual
      apply witness.outputsDiffer
      rw [suppliedActualEq, suppliedAlternateEq]
      exact outputsEqual

theorem functional_uptake_implies_r2
    {B : StaticBase} {I : InformationLayer B}
    {R : RepresentationLayer I}
    {F : SelfReferenceFrame R}
    {A : CoherentReferenceAction F}
    {U : UptakeLayer.{uU} F A}
    {c d : B.Center}
    (uptake : FunctionalUptake F A U c d) :
    ProspectiveDeSeEncoding F A c d :=
  uptake.1

/-- Exact faithful presentation makes the observed transition results differ,
    not merely the raw evaluator calls. -/
theorem functional_uptake_run_discrimination
    {B : StaticBase} {I : InformationLayer B}
    {R : RepresentationLayer I}
    {F : SelfReferenceFrame R}
    {A : CoherentReferenceAction F}
    {U : UptakeLayer.{uU} F A}
    {c d : B.Center}
    (uptake : FunctionalUptake F A U c d) :
    ∃ actual alternate : ProspectiveFunctionalInput F c d,
      LawfulProspectiveInput F c d actual ∧
      LawfulProspectiveInput F c d alternate ∧
      actual.eraseDeSe = alternate.eraseDeSe ∧
      U.run c d actual ≠ U.run c d alternate := by
  obtain ⟨_, actual, alternate, actualLawful, alternateLawful, _,
    sameErasure, _, actualPresented, alternatePresented, outputsDiffer⟩ := uptake
  refine ⟨actual, alternate, actualLawful, alternateLawful,
    sameErasure, ?_⟩
  simp only [UptakeLayer.run, actualPresented, alternatePresented, Option.map]
  intro equalResults
  exact outputsDiffer (Option.some.inj equalResults)

/-- Factorization through forecast context would erase the transported
    reference.  R3 supplies a constructive counterexample to that factorization. -/
def FactorsThroughDeSeErasure
    {B : StaticBase} {I : InformationLayer B}
    {R : RepresentationLayer I}
    {F : SelfReferenceFrame R}
    {A : CoherentReferenceAction F}
    (U : UptakeLayer.{uU} F A)
    (c d : B.Center) : Prop :=
  ∃ neutralEvaluate : I.ForecastToken → Option U.Output,
    ∀ input : ProspectiveFunctionalInput F c d,
      LawfulProspectiveInput F c d input →
      U.run c d input = neutralEvaluate input.eraseDeSe

theorem functional_uptake_not_factors_through_erasure
    {B : StaticBase} {I : InformationLayer B}
    {R : RepresentationLayer I}
    {F : SelfReferenceFrame R}
    {A : CoherentReferenceAction F}
    {U : UptakeLayer.{uU} F A}
    {c d : B.Center}
    (uptake : FunctionalUptake F A U c d) :
    ¬ FactorsThroughDeSeErasure U c d := by
  obtain ⟨actual, alternate, actualLawful, alternateLawful,
    sameErasure, resultsDiffer⟩ :=
    functional_uptake_run_discrimination uptake
  rintro ⟨neutralEvaluate, factors⟩
  apply resultsDiffer
  calc
    U.run c d actual = neutralEvaluate actual.eraseDeSe :=
      factors actual actualLawful
    _ = neutralEvaluate alternate.eraseDeSe :=
      congrArg neutralEvaluate sameErasure
    _ = U.run c d alternate := (factors alternate alternateLawful).symm

theorem functional_uptake_remode
    {B : StaticBase} {I : InformationLayer B}
    {R : RepresentationLayer I}
    {F : SelfReferenceFrame R}
    {A : CoherentReferenceAction F}
    (U : UptakeLayer.{uU} F A)
    (newMode : R.RepNode → EpistemicMode)
    (c d : B.Center) :
    FunctionalUptake (F.remode newMode) (A.remode newMode)
        (U.remode newMode) c d ↔
      FunctionalUptake F A U c d := by
  constructor
  · rintro ⟨r2, actualTarget, alternateTarget, actualLawful,
      alternateLawful, actualReference, sameErasure, referencesDiffer,
      actualPresented, alternatePresented, outputsDiffer⟩
    let actual := actualTarget.ofRemode newMode
    let alternate := alternateTarget.ofRemode newMode
    have actualBack : actual.remode newMode = actualTarget :=
      ProspectiveFunctionalInput.remode_ofRemode newMode actualTarget
    have alternateBack : alternate.remode newMode = alternateTarget :=
      ProspectiveFunctionalInput.remode_ofRemode newMode alternateTarget
    refine ⟨(prospective_de_se_remode newMode c d).mp r2,
      actual, alternate, ?_, ?_, actualReference, sameErasure,
      referencesDiffer, ?_, ?_, ?_⟩
    · apply (UptakeLayer.lawful_input_remode newMode actual).mp
      rw [actualBack]
      exact actualLawful
    · apply (UptakeLayer.lawful_input_remode newMode alternate).mp
      rw [alternateBack]
      exact alternateLawful
    · apply (U.present_remode newMode actual actual).mp
      rw [actualBack]
      exact actualPresented
    · apply (U.present_remode newMode alternate alternate).mp
      rw [alternateBack]
      exact alternatePresented
    · intro equalOutputs
      apply outputsDiffer
      have actualEvaluation :
          (U.remode newMode).evaluate c d actualTarget =
            U.evaluate c d actual := by
        rw [← actualBack]
        exact U.evaluate_remode newMode actual
      have alternateEvaluation :
          (U.remode newMode).evaluate c d alternateTarget =
            U.evaluate c d alternate := by
        rw [← alternateBack]
        exact U.evaluate_remode newMode alternate
      exact actualEvaluation.trans
        (equalOutputs.trans alternateEvaluation.symm)
  · rintro ⟨r2, actual, alternate, actualLawful, alternateLawful,
      actualReference, sameErasure, referencesDiffer,
      actualPresented, alternatePresented, outputsDiffer⟩
    refine ⟨(prospective_de_se_remode newMode c d).mpr r2,
      actual.remode newMode, alternate.remode newMode,
      (UptakeLayer.lawful_input_remode newMode actual).mpr actualLawful,
      (UptakeLayer.lawful_input_remode newMode alternate).mpr alternateLawful,
      actualReference, sameErasure, referencesDiffer,
      (U.present_remode newMode actual actual).mpr actualPresented,
      (U.present_remode newMode alternate alternate).mpr alternatePresented,
      ?_⟩
    intro equalOutputs
    apply outputsDiffer
    exact (U.evaluate_remode newMode actual).symm.trans
      (equalOutputs.trans (U.evaluate_remode newMode alternate))

end StaticRole
