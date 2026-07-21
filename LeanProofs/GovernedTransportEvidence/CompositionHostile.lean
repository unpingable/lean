/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE

  Finite hostile models for composition coherence and exact coverage repair.
  Every model names the precise laundering shortcut it defeats.
-/

import LeanProofs.GovernedTransport.CoverageRepair
import LeanProofs.GovernedTransportEvidence.Hostile

namespace LeanProofs.GovernedTransport.CompositionHostile

open LeanProofs.GovernedTransport

/-! ## An upstream gap can be irrelevant to the used downstream region -/

namespace IrrelevantUpstreamGap

/-- The first leg omits `true`. -/
def first : Span Unit Bool where
  Witness := Unit
  source _ := ()
  target _ := false

def trueGap : ExhibitedGap first := by
  refine ⟨true, ?_⟩
  intro fiber
  exact Bool.noConfusion fiber.mapsTo

/-- The only final target is reached entirely through covered intermediate
    candidate `false`; no final route uses omitted candidate `true`. -/
def second : Span Bool Unit where
  Witness := Unit
  source _ := false
  target _ := ()

def compositeCovered : TargetCovered (first.compose second) :=
  fun _ =>
    ⟨{ firstWitness := ()
       secondWitness := ()
       compatible := rfl },
      rfl⟩

/-- Defeats unconditional upstream-gap propagation: an upstream omission does
    not obstruct a final target whose every route stays in the covered
    intermediate region. -/
theorem upstream_gap_can_be_irrelevant :
    Nonempty (ExhibitedGap first) ∧
      Nonempty (TargetCovered (first.compose second)) :=
  ⟨⟨trueGap⟩, ⟨compositeCovered⟩⟩

end IrrelevantUpstreamGap

/-! ## Endpoint equality does not preserve fibers -/

namespace EndpointOnlyBridge

def complete : Span Bool Bool where
  Witness := Bool
  source witness := witness
  target witness := witness

def incomplete : Span Bool Bool where
  Witness := Bool
  source witness := witness
  target _ := false

/-- Even the witness types are exactly equivalent.  What fails is preservation
    of the proof-relevant target leg at witness `true`. -/
def witnessEquiv : ExactEquiv complete.Witness incomplete.Witness where
  toFun witness := witness
  invFun witness := witness
  left_inv _ := rfl
  right_inv _ := rfl

def completeCoverage : TargetCovered complete :=
  fun target => ⟨target, rfl⟩

def incompleteTrueGap : ExhibitedGap incomplete := by
  refine ⟨true, ?_⟩
  intro fiber
  exact Bool.noConfusion fiber.mapsTo

/-- Both spans have exactly the same endpoint types, yet one is covered and
    the other has an exhibited target gap.  Endpoint agreement is therefore
    weaker than a fiber-preserving bridge equivalence. -/
theorem equal_endpoint_types_do_not_preserve_fibers :
    Nonempty (ExactEquiv complete.Witness incomplete.Witness) ∧
      Nonempty (TargetCovered complete) ∧
      Nonempty (ExhibitedGap incomplete) :=
  ⟨⟨witnessEquiv⟩, ⟨completeCoverage⟩, ⟨incompleteTrueGap⟩⟩

end EndpointOnlyBridge

/-! ## Equal composite endpoints do not identify nested route witnesses -/

namespace EndpointOnlyAssociativity

def first : Span Unit Unit where
  Witness := Bool
  source _ := ()
  target _ := ()

def second : Span Unit Unit where
  Witness := Bool
  source _ := ()
  target _ := ()

def third : Span Unit Unit where
  Witness := Bool
  source _ := ()
  target _ := ()

def leftFalse : ((first.compose second).compose third).Witness where
  firstWitness :=
    { firstWitness := false
      secondWitness := false
      compatible := rfl }
  secondWitness := false
  compatible := rfl

def leftTrue : ((first.compose second).compose third).Witness where
  firstWitness :=
    { firstWitness := true
      secondWitness := false
      compatible := rfl }
  secondWitness := false
  compatible := rfl

def firstRouteTag
    (route : ((first.compose second).compose third).Witness) : Bool :=
  route.firstWitness.firstWitness

/-- Defeats associativity-by-endpoint laundering.  These witnesses share the
    same composite source and target, but carry different first-route data;
    an honest associator must map the nested witnesses explicitly. -/
theorem equal_composite_endpoints_do_not_identify_routes :
    ((first.compose second).compose third).source leftFalse =
        ((first.compose second).compose third).source leftTrue ∧
      ((first.compose second).compose third).target leftFalse =
        ((first.compose second).compose third).target leftTrue ∧
      firstRouteTag leftFalse ≠ firstRouteTag leftTrue := by
  exact ⟨rfl, rfl, Bool.noConfusion⟩

end EndpointOnlyAssociativity

/-! ## Target-local evidence is not transported coverage repair -/

namespace TargetLocalSubstitution

def first : Span Unit Bool where
  Witness := Unit
  source _ := ()
  target _ := false

def second : Span Bool Bool where
  Witness := Bool
  source witness := witness
  target witness := witness

def compositeTrueGap : ExhibitedGap (first.compose second) := by
  refine ⟨true, ?_⟩
  intro fiber
  have false_eq_second : false = fiber.preimage.secondWitness :=
    fiber.preimage.compatible
  exact Bool.noConfusion (false_eq_second.trans fiber.mapsTo)

def TargetLocalEvidence (_ : Bool) : Type := Unit

def targetLocalEvidence : GlobalBlocked Bool TargetLocalEvidence :=
  fun _ => ()

/-- Complete target-local evidence can coexist with the same exact composite
    gap.  It neither supplies an upstream witness nor repairs transported
    coverage from the original source. -/
theorem target_local_evidence_does_not_repair_transport :
    Nonempty (GlobalBlocked Bool TargetLocalEvidence) ∧
      Nonempty (ExhibitedGap (first.compose second)) :=
  ⟨⟨targetLocalEvidence⟩, ⟨compositeTrueGap⟩⟩

end TargetLocalSubstitution

/-! ## Exact repair is local to the route it adds -/

namespace LocalRepair

def originalFirst : Span Unit Bool where
  Witness := Empty
  source witness := nomatch witness
  target witness := nomatch witness

/-- The extension adds exactly one upstream route, reaching only `false`. -/
def extendedFirst : Span Unit Bool where
  Witness := Unit
  source _ := ()
  target _ := false

def second : Span Bool Bool where
  Witness := Bool
  source witness := witness
  target witness := witness

def originalFalseGap : ExhibitedGap (originalFirst.compose second) := by
  refine ⟨false, ?_⟩
  intro fiber
  exact nomatch fiber.preimage.firstWitness

def extension : CoverageExtension originalFirst extendedFirst where
  includeWitness witness := nomatch witness
  include_injective := by
    intro left
    exact nomatch left
  source_preserved witness := nomatch witness
  target_preserved witness := nomatch witness

def falseRoute : EndToEndFiber extendedFirst second false where
  secondWitness := false
  firstFiber := ⟨(), rfl⟩
  reachesTarget := rfl

def exactRepair : ExactCompositeRepair originalFirst extendedFirst second where
  originalGap := originalFalseGap
  extension := extension
  addedRoute := falseRoute

def repairedFalseFiber :
    Fiber (extendedFirst.compose second).target false :=
  repaired_composite_fiber exactRepair

def trueGapAfterRepair : ExhibitedGap (extendedFirst.compose second) := by
  refine ⟨true, ?_⟩
  intro fiber
  have false_eq_second : false = fiber.preimage.secondWitness :=
    fiber.preimage.compatible
  exact Bool.noConfusion (false_eq_second.trans fiber.mapsTo)

/-- Defeats repair globalization.  The provenance-bearing added route repairs
    `false`, while unrelated target `true` remains constructively uncovered. -/
theorem one_repaired_target_does_not_globalize :
    Nonempty (Fiber (extendedFirst.compose second).target false) ∧
      Nonempty (ExhibitedGap (extendedFirst.compose second)) ∧
      ¬ Nonempty (TargetCovered (extendedFirst.compose second)) := by
  refine ⟨⟨repairedFalseFiber⟩, ⟨trueGapAfterRepair⟩, ?_⟩
  rintro ⟨covered⟩
  exact target_covered_excludes_gap covered trueGapAfterRepair

end LocalRepair

/-! ## Leg preservation without witness injectivity rewrites route history -/

namespace CollapsingExtension

def original : Span Unit Unit where
  Witness := Bool
  source _ := ()
  target _ := ()

def collapsed : Span Unit Unit where
  Witness := Unit
  source _ := ()
  target _ := ()

def collapsingInclusion (_ : original.Witness) : collapsed.Witness := ()

/-- Source and target legs alone permit two distinct old routes to collapse to
    one.  The injectivity field of `CoverageExtension` rejects that history
    rewrite. -/
theorem leg_preservation_without_injectivity_rewrites_route_history :
    (∀ witness,
      collapsed.source (collapsingInclusion witness) = original.source witness) ∧
      (∀ witness,
        collapsed.target (collapsingInclusion witness) = original.target witness) ∧
      collapsingInclusion false = collapsingInclusion true ∧
      ¬ Nonempty (CoverageExtension original collapsed) := by
  refine ⟨fun _ => rfl, fun _ => rfl, rfl, ?_⟩
  rintro ⟨extension⟩
  have collapsedRoutes :
      extension.includeWitness false = extension.includeWitness true := by
    cases extension.includeWitness false
    cases extension.includeWitness true
    rfl
  exact Bool.noConfusion (extension.include_injective collapsedRoutes)

end CollapsingExtension

/-! ## Finite executable coverage decisions -/

namespace FiniteCoverage

def one : Span Unit Bool where
  Witness := Unit
  source _ := ()
  target _ := false

/-- This function computes because the target and witness behavior are the
    displayed finite Bool specimen; it is not a generic decision procedure. -/
def decideOne : (target : Bool) → DecidedCoverage one target
  | false => .covered ⟨(), rfl⟩
  | true => .gap (fun fiber => Bool.noConfusion fiber.mapsTo)

theorem finite_check_returns_exact_branches :
    decideOne false = .covered ⟨(), rfl⟩ ∧
      decideOne true = .gap (fun fiber => Bool.noConfusion fiber.mapsTo) :=
  ⟨rfl, rfl⟩

end FiniteCoverage

/-! ## An outstanding receipt is not an exhibited gap -/

namespace MissingReceipt

def complete : Span Bool Bool where
  Witness := Bool
  source witness := witness
  target witness := witness

def covered : TargetCovered complete :=
  fun target => ⟨target, rfl⟩

def obligation (target : Bool) : CoverageObligation complete target :=
  .outstanding

/-- Defeats absence-as-gap.  An outstanding receipt token exists at `true`
    even though `true` has an exact fiber and no exhibited gap can exist. -/
theorem missing_receipt_does_not_exhibit_debt :
    Nonempty (CoverageObligation complete true) ∧
      Nonempty (CoveredTarget complete true) ∧
      ¬ Nonempty (ExhibitedGap complete) := by
  refine ⟨⟨obligation true⟩, ⟨covered true⟩, ?_⟩
  rintro ⟨gap⟩
  exact target_covered_excludes_gap covered gap

end MissingReceipt

/-! ## Image-relative blockage survives an outstanding obligation -/

namespace ImageBlockageWithObligation

def trueObligation :
    CoverageObligation Hostile.UnitBool.crossing true :=
  .outstanding

/-- Exact image-relative blockage remains available while coverage of `true`
    is outstanding.  The evidence cannot be presented as target-global
    blockage because the target-local negative family has no `true` witness. -/
theorem image_blockage_survives_without_globalization :
    Nonempty
        (BlockedAlong Hostile.UnitBool.crossing
          Hostile.UnitBool.TargetNegative) ∧
      Nonempty (CoverageObligation Hostile.UnitBool.crossing true) ∧
      ¬ Nonempty (GlobalBlocked Bool Hostile.UnitBool.TargetNegative) := by
  refine ⟨⟨Hostile.UnitBool.blockedOnImage⟩, ⟨trueObligation⟩, ?_⟩
  rintro ⟨blocked⟩
  exact nomatch blocked true

end ImageBlockageWithObligation

/-! ## Constructor-only debt algebra is scientifically empty -/

namespace ConstructorDebt

inductive DebtToken where
  | outstanding
  | exhibited
  deriving DecidableEq

/-- A deliberately bad candidate operation: it simply projects the upstream
    constructor and ignores all downstream route structure. -/
def compose (upstream _downstream : DebtToken) : DebtToken := upstream

theorem projection_is_associative
    (first second third : DebtToken) :
    compose (compose first second) third =
      compose first (compose second third) :=
  rfl

theorem projection_discards_downstream (upstream downstream : DebtToken) :
    compose upstream downstream = upstream :=
  rfl

/-- The attractive algebraic law above carries no information about whether
    a downstream route uses or avoids an omitted intermediate candidate. -/
theorem associative_projection_is_route_blind :
    compose .outstanding .exhibited = .outstanding ∧
      compose .outstanding .outstanding = .outstanding :=
  ⟨rfl, rfl⟩

end ConstructorDebt

#print axioms IrrelevantUpstreamGap.upstream_gap_can_be_irrelevant
#print axioms EndpointOnlyBridge.equal_endpoint_types_do_not_preserve_fibers
#print axioms EndpointOnlyAssociativity.equal_composite_endpoints_do_not_identify_routes
#print axioms TargetLocalSubstitution.target_local_evidence_does_not_repair_transport
#print axioms LocalRepair.one_repaired_target_does_not_globalize
#print axioms CollapsingExtension.leg_preservation_without_injectivity_rewrites_route_history
#print axioms FiniteCoverage.finite_check_returns_exact_branches
#print axioms MissingReceipt.missing_receipt_does_not_exhibit_debt
#print axioms ImageBlockageWithObligation.image_blockage_survives_without_globalization
#print axioms ConstructorDebt.projection_is_associative
#print axioms ConstructorDebt.projection_discards_downstream
#print axioms ConstructorDebt.associative_projection_is_route_blind

end LeanProofs.GovernedTransport.CompositionHostile
