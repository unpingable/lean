/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE

  Finite hostile and nearby control models for the promoted internal core.
  Each model removes one laundering shortcut while leaving the reusable
  vocabulary open to incomplete and adversarial instances.
-/

import LeanProofs.GovernedTransport.Positive
import LeanProofs.GovernedTransport.Residue
import LeanProofs.GovernedTransport.Composition
import LeanProofs.GovernedTransport.Federation

namespace LeanProofs.GovernedTransport.Hostile

open LeanProofs.GovernedTransport

/-! ## Positive source witness without a licensed crossing lift -/

namespace MissingPositiveLift

def crossing : Span Unit Bool where
  Witness := Empty
  source witness := nomatch witness
  target witness := nomatch witness

def SourcePositive (_ : Unit) : Type := Unit
def TargetPositive (_ : Bool) : Type := Empty

def sourceRealized : Realized Unit SourcePositive := ⟨(), ()⟩

theorem certificate_lift_fails :
    CertificateLift crossing SourcePositive → False := by
  intro lift
  exact nomatch (lift () ()).preimage

theorem target_realization_fails :
    Realized Bool TargetPositive → False := by
  rintro ⟨_, positive⟩
  exact nomatch positive

/-- A source candidate and certificate do not cross an empty licensed route. -/
theorem source_witness_without_lift_does_not_transport :
    Nonempty (Realized Unit SourcePositive) ∧
      ¬ Nonempty (CertificateLift crossing SourcePositive) ∧
      ¬ Nonempty (Realized Bool TargetPositive) := by
  refine ⟨⟨sourceRealized⟩, ?_, ?_⟩
  · rintro ⟨lift⟩
    exact certificate_lift_fails lift
  · rintro ⟨realized⟩
    exact target_realization_fails realized

end MissingPositiveLift

/-! ## One-to-Bool: image blockage is not global blockage -/

namespace UnitBool

def SourceNegative (_ : Unit) : Type := Unit

inductive ImportedNegative : Bool → Type where
  | rejectedFalse : ImportedNegative false

inductive TargetNegative : Bool → Type where
  | reliedFalse : TargetNegative false

def crossing : Span Unit Bool where
  Witness := Unit
  source _ := ()
  target _ := false

def sourceBlocked : GlobalBlocked Unit SourceNegative := fun _ => ()

def translate : TranslateAlong crossing SourceNegative ImportedNegative :=
  fun _ _ => .rejectedFalse

def rely : RelyLocally ImportedNegative TargetNegative := by
  intro target imported
  cases imported
  exact .reliedFalse

def transported : TransportedBlockage crossing SourceNegative
    ImportedNegative TargetNegative :=
  partial_negative_transport sourceBlocked translate rely

def blockedOnImage : BlockedAlong crossing TargetNegative :=
  transported.blockedAlong

def trueGap : ExhibitedGap crossing := by
  refine ⟨true, ?_⟩
  intro alleged
  cases alleged.preimage
  exact Bool.noConfusion alleged.mapsTo

def coverageDecision : CoverageDecision crossing := .inr trueGap

def incompleteOutcome : NegativeTransportOutcome crossing transported :=
  negative_transport_of_coverage_decision transported coverageDecision

theorem target_global_blockage_fails :
    GlobalBlocked Bool TargetNegative → False := by
  intro blocked
  exact nomatch blocked true

theorem target_coverage_fails : TargetCovered crossing → False := by
  intro covered
  exact target_covered_excludes_gap covered trueGap

/-- **No free global transport.** -/
theorem no_free_global_block_transport :
    Nonempty (GlobalBlocked Unit SourceNegative) ∧
      Nonempty (BlockedAlong crossing TargetNegative) ∧
      ¬ Nonempty (GlobalBlocked Bool TargetNegative) := by
  refine ⟨⟨sourceBlocked⟩, ⟨blockedOnImage⟩, ?_⟩
  rintro ⟨blocked⟩
  exact target_global_blockage_fails blocked

theorem incomplete_decision_returns_exhibited_debt :
    incompleteOutcome.resolve = .inl (.exhibited trueGap) := rfl

end UnitBool

/-! ## Target-local blockage cannot masquerade as transported evidence -/

namespace TargetLocalRegression

def EmptySourceNegative (_ : Unit) : Type := Empty
def ImportedNegative (_ : Bool) : Type := Unit
def TargetLocalNegative (_ : Bool) : Type := Unit

def targetLocalBlocked : GlobalBlocked Bool TargetLocalNegative := fun _ => ()

def noTransportedBlockage
    (alleged : TransportedBlockage UnitBool.crossing EmptySourceNegative
      ImportedNegative TargetLocalNegative) : False :=
  nomatch alleged.sourceBlocked ()

/-- Regression for the GT-0 hostile-review defect: complete target-local
    evidence cannot inhabit transported blockage without source evidence. -/
theorem target_local_block_cannot_masquerade_as_transport :
    Nonempty (GlobalBlocked Bool TargetLocalNegative) ∧
      ¬ Nonempty (TransportedBlockage UnitBool.crossing
        EmptySourceNegative ImportedNegative TargetLocalNegative) := by
  refine ⟨⟨targetLocalBlocked⟩, ?_⟩
  rintro ⟨alleged⟩
  exact noTransportedBlockage alleged

end TargetLocalRegression

/-! ## Finite coverage decisions and the meaning of outstanding debt -/

namespace FiniteCoverageDecision

def complete : Span Bool Bool where
  Witness := Bool
  source witness := witness
  target witness := witness

def completeCoverage : TargetCovered complete :=
  fun target => ⟨target, rfl⟩

def SourceNegative (_ : Bool) : Type := Unit
def ImportedNegative (_ : Bool) : Type := Unit
def TargetNegative (_ : Bool) : Type := Unit

def transported : TransportedBlockage complete SourceNegative
    ImportedNegative TargetNegative where
  sourceBlocked _ := ()
  translate _ _ := ()
  rely _ _ := ()

def completeDecision : CoverageDecision complete := .inl completeCoverage

def completeOutcome : NegativeTransportOutcome complete transported :=
  negative_transport_of_coverage_decision transported completeDecision

theorem complete_decision_returns_global_blockage :
    completeOutcome.resolve = .inr (transported.globalize completeCoverage) :=
  rfl

theorem complete_has_no_exhibited_gap : ExhibitedGap complete → False :=
  fun gap => target_covered_excludes_gap completeCoverage gap

/-- Outstanding debt records a missing receipt at a boundary; it is not a
    negative coverage decision and may coexist with actual coverage. -/
theorem outstanding_does_not_manufacture_gap :
    Nonempty (CoverageDebt complete) ∧
      Nonempty (TargetCovered complete) ∧
      ¬ Nonempty (ExhibitedGap complete) := by
  refine ⟨⟨.outstanding⟩, ⟨completeCoverage⟩, ?_⟩
  rintro ⟨gap⟩
  exact complete_has_no_exhibited_gap gap

end FiniteCoverageDecision

/-! ## Pullback composition and inherited omission -/

namespace CompositionDebt

/-- Upstream reaches only `d1 = false`; `d2 = true` is omitted. -/
def first : Span Unit Bool where
  Witness := Unit
  source _ := ()
  target _ := false

/-- Downstream is locally target-covering, with each final target reached only
    from the equal intermediate candidate. -/
def second : Span Bool Bool where
  Witness := Bool
  source witness := witness
  target witness := witness

def secondCovered : TargetCovered second :=
  fun target => ⟨target, rfl⟩

def firstTrueGap : ExhibitedGap first := by
  refine ⟨true, ?_⟩
  intro alleged
  exact Bool.noConfusion alleged.mapsTo

def compositeTrueGap : ExhibitedGap (first.compose second) := by
  refine ⟨true, ?_⟩
  intro alleged
  have false_eq_second : false = alleged.preimage.secondWitness :=
    alleged.preimage.compatible
  have second_eq_true : alleged.preimage.secondWitness = true :=
    alleged.mapsTo
  exact Bool.noConfusion (false_eq_second.trans second_eq_true)

theorem composite_target_coverage_fails :
    TargetCovered (first.compose second) → False :=
  fun covered => target_covered_excludes_gap covered compositeTrueGap

theorem downstream_coverage_does_not_cover_composite :
    Nonempty (TargetCovered second) ∧
      ¬ Nonempty (TargetCovered (first.compose second)) := by
  refine ⟨⟨secondCovered⟩, ?_⟩
  rintro ⟨covered⟩
  exact composite_target_coverage_fails covered

/-- **Inherited omission survives.**  The clean downstream bridge cannot
    fund the intermediate candidate excluded upstream. -/
theorem inherited_debt_survives_clean_downstream :
    Nonempty (TargetCovered second) ∧
      Nonempty (ExhibitedGap (first.compose second)) :=
  ⟨⟨secondCovered⟩, ⟨compositeTrueGap⟩⟩

/-- A repaired first bridge adds an exact route to each intermediate
    candidate; it does not merely relabel the downstream bridge complete. -/
def repairedFirst : Span Unit Bool where
  Witness := Bool
  source _ := ()
  target witness := witness

def repairedFirstCovered : TargetCovered repairedFirst :=
  fun target => ⟨target, rfl⟩

def repairedCompositeCovered : TargetCovered (repairedFirst.compose second) :=
  both_leg_coverage_implies_composite_coverage
    repairedFirstCovered secondCovered

def repairedTrueRoute : EndToEndFiber repairedFirst second true where
  secondWitness := true
  firstFiber := ⟨true, rfl⟩
  reachesTarget := rfl

/-- An upstream omission is repaired by supplying the formerly missing exact
    compatible route. -/
theorem exact_route_repairs_omitted_region :
    Nonempty (ExhibitedGap (first.compose second)) ∧
      Nonempty (TargetCovered (repairedFirst.compose second)) ∧
      Nonempty (Fiber (repairedFirst.compose second).target true) :=
  ⟨⟨compositeTrueGap⟩, ⟨repairedCompositeCovered⟩,
    ⟨composite_fiber_of_end_to_end_route repairedTrueRoute⟩⟩

end CompositionDebt

/-! ## Tagged federation -/

namespace Federation

def LocalCandidate (_ : Bool) : Type := Unit
abbrev Candidate := FederationCandidate Bool LocalCandidate

def leftInclusion : Span Unit Candidate :=
  localInclusion (Candidate := LocalCandidate) false

def rightGap : ExhibitedGap leftInclusion := by
  refine ⟨⟨true, ()⟩, ?_⟩
  intro alleged
  have index_eq : false = true :=
    congrArg (fun candidate : Candidate => candidate.1) alleged.mapsTo
  exact Bool.noConfusion index_eq

def EverywhereNegative (_ : Candidate) : Type := Unit

def federationBlockedEverywhere :
    GlobalBlocked Candidate EverywhereNegative := fun _ => ()

/-- Noncoverage of one local inclusion alone does not refute federation-global
    blockage. -/
theorem noncoverage_does_not_refute_global_blockage :
    Nonempty (ExhibitedGap leftInclusion) ∧
      Nonempty (GlobalBlocked Candidate EverywhereNegative) :=
  ⟨⟨rightGap⟩, ⟨federationBlockedEverywhere⟩⟩

def LeftOnlyNegative : Candidate → Type
  | ⟨false, _⟩ => Unit
  | ⟨true, _⟩ => Empty

def RightOnlyPositive : Candidate → Type
  | ⟨false, _⟩ => Empty
  | ⟨true, _⟩ => Unit

def localSourceNegative (_ : Unit) : Type := Unit
def localSourceBlocked : GlobalBlocked Unit localSourceNegative := fun _ => ()

def ImportedLeftNegative : Candidate → Type
  | ⟨false, _⟩ => Unit
  | ⟨true, _⟩ => Empty

def leftTranslate :
    TranslateAlong leftInclusion localSourceNegative ImportedLeftNegative :=
  fun _ _ => ()

def leftRely : RelyLocally ImportedLeftNegative LeftOnlyNegative := by
  intro candidate imported
  obtain ⟨index, localCandidate⟩ := candidate
  cases index
  · exact imported
  · exact nomatch imported

def localTransported : TransportedBlockage leftInclusion localSourceNegative
    ImportedLeftNegative LeftOnlyNegative :=
  partial_negative_transport localSourceBlocked leftTranslate leftRely

def rightRealized : Realized Candidate RightOnlyPositive :=
  ⟨⟨true, ()⟩, ()⟩

theorem positive_negative_exclusive (candidate : Candidate) :
    RightOnlyPositive candidate → LeftOnlyNegative candidate → False := by
  obtain ⟨index, localCandidate⟩ := candidate
  cases index <;> intro positive negative
  · exact nomatch positive
  · exact nomatch negative

theorem right_realization_refutes_federation_global_blockage :
    GlobalBlocked Candidate LeftOnlyNegative → False := by
  intro blocked
  exact positive_negative_exclusive rightRealized.1 rightRealized.2
    (blocked rightRealized.1)

/-- A local certificate and exact transported image blockage cannot establish
    a global claim over the uncovered tagged jurisdiction. -/
theorem local_block_does_not_globalize :
    Nonempty (GlobalBlocked Unit localSourceNegative) ∧
      Nonempty (BlockedAlong leftInclusion LeftOnlyNegative) ∧
      Nonempty (Realized Candidate RightOnlyPositive) ∧
      ¬ Nonempty (GlobalBlocked Candidate LeftOnlyNegative) := by
  refine ⟨⟨localSourceBlocked⟩, ⟨localTransported.blockedAlong⟩,
    ⟨rightRealized⟩, ?_⟩
  rintro ⟨blocked⟩
  exact right_realization_refutes_federation_global_blockage blocked

end Federation

/-! ## Same endpoints do not identify route-carried force -/

namespace SameEndpointRoutes

def routes : Span Unit Unit where
  Witness := Bool
  source _ := ()
  target _ := ()

def SourceArtifact (_ : Unit) : Type := Unit
def RouteArtifact (_ : Unit) : Type := Bool

def translate : TranslateAlong routes SourceArtifact RouteArtifact :=
  fun route _ => route

def sourceRealized : Realized Unit SourceArtifact := ⟨(), ()⟩

def falseLift : CertificateLift routes SourceArtifact :=
  fun _ _ => ⟨false, rfl⟩

def trueLift : CertificateLift routes SourceArtifact :=
  fun _ _ => ⟨true, rfl⟩

def falseTransport : Realized Unit RouteArtifact :=
  translated_realization_of_certificate_lift
    falseLift translate sourceRealized

def trueTransport : Realized Unit RouteArtifact :=
  translated_realization_of_certificate_lift
    trueLift translate sourceRealized

/-- Equal source and target candidates do not erase route-sensitive carried
    artifacts.  Route fungibility would require an additional receipt. -/
theorem same_endpoints_do_not_identify_transported_force :
    falseTransport.1 = trueTransport.1 ∧
      falseTransport.2 ≠ trueTransport.2 := by
  refine ⟨rfl, ?_⟩
  exact Bool.noConfusion

end SameEndpointRoutes

#print axioms MissingPositiveLift.certificate_lift_fails
#print axioms MissingPositiveLift.target_realization_fails
#print axioms MissingPositiveLift.source_witness_without_lift_does_not_transport
#print axioms UnitBool.target_global_blockage_fails
#print axioms UnitBool.target_coverage_fails
#print axioms UnitBool.no_free_global_block_transport
#print axioms UnitBool.incomplete_decision_returns_exhibited_debt
#print axioms TargetLocalRegression.target_local_block_cannot_masquerade_as_transport
#print axioms FiniteCoverageDecision.complete_decision_returns_global_blockage
#print axioms FiniteCoverageDecision.complete_has_no_exhibited_gap
#print axioms FiniteCoverageDecision.outstanding_does_not_manufacture_gap
#print axioms CompositionDebt.composite_target_coverage_fails
#print axioms CompositionDebt.downstream_coverage_does_not_cover_composite
#print axioms CompositionDebt.inherited_debt_survives_clean_downstream
#print axioms CompositionDebt.exact_route_repairs_omitted_region
#print axioms Federation.noncoverage_does_not_refute_global_blockage
#print axioms Federation.positive_negative_exclusive
#print axioms Federation.right_realization_refutes_federation_global_blockage
#print axioms Federation.local_block_does_not_globalize
#print axioms SameEndpointRoutes.same_endpoints_do_not_identify_transported_force

end LeanProofs.GovernedTransport.Hostile
