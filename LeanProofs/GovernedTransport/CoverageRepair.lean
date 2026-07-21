/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: STABLE-SURFACE

  Exact coverage propagation and provenance-bearing repair.  An outstanding
  obligation is not an exhibited gap, and a repair extends witnessed routes
  rather than rewriting the original crossing.
-/

import LeanProofs.GovernedTransport.Composition

namespace LeanProofs.GovernedTransport

universe u v z w₁ w₂ w₃

/-- One named target whose coverage receipt is still requested.  The token
    contains no negative evidence and may coexist with an exact target fiber. -/
inductive CoverageObligation
    {Source : Type u} {Target : Type v}
    (B : Span.{u, v, w₁} Source Target) (target : Target) : Type where
  | outstanding : CoverageObligation B target

/-- Exact positive coverage at one named target. -/
abbrev CoveredTarget
    {Source : Type u} {Target : Type v}
    (B : Span.{u, v, w₁} Source Target) (target : Target) :=
  Fiber B.target target

/-- A target-specific constructive decision.  This is witnessed data, not a
    claim that arbitrary spans admit an executable decision procedure. -/
inductive DecidedCoverage
    {Source : Type u} {Target : Type v}
    (B : Span.{u, v, w₁} Source Target) (target : Target) : Type (max w₁ v) where
  | covered (fiber : CoveredTarget B target) : DecidedCoverage B target
  | gap (unreachable : CoveredTarget B target → Empty) :
      DecidedCoverage B target

/-- A downstream fiber is the final-leg component of an exact composite
    fiber. -/
def downstream_fiber_of_composite_fiber
    {Source : Type u} {Middle : Type v} {Target : Type z}
    {first : Span.{u, v, w₁} Source Middle}
    {second : Span.{v, z, w₂} Middle Target}
    {target : Target}
    (fiber : Fiber (first.compose second).target target) :
    Fiber second.target target :=
  ⟨fiber.preimage.secondWitness, fiber.mapsTo⟩

/-- Composite target coverage projects constructively to downstream target
    coverage. -/
def downstream_covered_of_composite_covered
    {Source : Type u} {Middle : Type v} {Target : Type z}
    {first : Span.{u, v, w₁} Source Middle}
    {second : Span.{v, z, w₂} Middle Target}
    (covered : TargetCovered (first.compose second)) : TargetCovered second :=
  fun target => downstream_fiber_of_composite_fiber (covered target)

/-- A named downstream omission is necessarily an omission of the composite. -/
def downstream_gap_propagates
    {Source : Type u} {Middle : Type v} {Target : Type z}
    {first : Span.{u, v, w₁} Source Middle}
    {second : Span.{v, z, w₂} Middle Target}
    (gap : ExhibitedGap second) : ExhibitedGap (first.compose second) := by
  obtain ⟨target, unreachable⟩ := gap
  exact ⟨target, fun fiber =>
    unreachable (downstream_fiber_of_composite_fiber fiber)⟩

/-- Exact evidence that one relevant downstream route starts in the named
    omitted intermediate region.  The named upstream gap must be causal; an
    unrelated per-route nonreachability proof is a different law and is not
    admitted here as omission propagation. -/
structure RouteOmission
    {Source : Type u} {Middle : Type v} {Target : Type z}
    (first : Span.{u, v, w₁} Source Middle)
    (second : Span.{v, z, w₂} Middle Target)
    (omitted : Middle) (secondWitness : second.Witness) :
    Type v where
  exactStart : second.source secondWitness = omitted

/-- Exact route-sensitive evidence needed to propagate one upstream omission.
    Every downstream witness reaching the named final target must start in
    the exact intermediate region omitted by the exhibited upstream gap. -/
def UniversalOmissionReceipt
    {Source : Type u} {Middle : Type v} {Target : Type z}
    (first : Span.{u, v, w₁} Source Middle)
    (second : Span.{v, z, w₂} Middle Target)
  (omitted : Middle) (target : Target) : Type (max v w₂) :=
  (secondWitness : second.Witness) →
    second.target secondWitness = target →
    RouteOmission first second omitted secondWitness

/-- An upstream gap propagates only through a universal receipt accounting for
    every downstream route to the named final target. -/
def upstream_gap_propagates_conditionally
    {Source : Type u} {Middle : Type v} {Target : Type z}
    {first : Span.{u, v, w₁} Source Middle}
    {second : Span.{v, z, w₂} Middle Target}
    (gap : ExhibitedGap first)
    (target : Target)
    (receipt : UniversalOmissionReceipt first second gap.1 target) :
    ExhibitedGap (first.compose second) := by
  refine ⟨target, ?_⟩
  intro compositeFiber
  have upstreamFiber :
      Fiber first.target
        (second.source compositeFiber.preimage.secondWitness) :=
    upstream_fiber_of_composite_fiber compositeFiber
  have exactStart :=
    (receipt compositeFiber.preimage.secondWitness
      compositeFiber.mapsTo).exactStart
  exact gap.2
    ⟨upstreamFiber.preimage,
      upstreamFiber.mapsTo.trans exactStart⟩

/-- A coverage-only extension injectively embeds every old witness while
    preserving both legs exactly.  It may add new witnesses, but it neither
    collapses nor alters old routes and claims no force-bearing correspondence
    beyond bare span geometry. -/
structure CoverageExtension
    {Source : Type u} {Target : Type v}
    (original : Span.{u, v, w₁} Source Target)
    (extended : Span.{u, v, w₂} Source Target) where
  includeWitness : original.Witness → extended.Witness
  include_injective :
    ∀ {left right}, includeWitness left = includeWitness right → left = right
  source_preserved : (witness : original.Witness) →
    extended.source (includeWitness witness) = original.source witness
  target_preserved : (witness : original.Witness) →
    extended.target (includeWitness witness) = original.target witness

namespace CoverageExtension

/-- Existing exact target fibers survive route extension. -/
def liftFiber
    {Source : Type u} {Target : Type v}
    {original : Span.{u, v, w₁} Source Target}
    {extended : Span.{u, v, w₂} Source Target}
    (extension : CoverageExtension original extended)
    {target : Target} (fiber : Fiber original.target target) :
    Fiber extended.target target :=
  ⟨extension.includeWitness fiber.preimage,
    (extension.target_preserved fiber.preimage).trans fiber.mapsTo⟩

/-- Global target coverage is monotone under exact route extension. -/
def liftCoverage
    {Source : Type u} {Target : Type v}
    {original : Span.{u, v, w₁} Source Target}
    {extended : Span.{u, v, w₂} Source Target}
    (extension : CoverageExtension original extended)
    (covered : TargetCovered original) : TargetCovered extended :=
  fun target => extension.liftFiber (covered target)

/-- A gap remaining after extension was already a gap before extension. -/
def restrictGap
    {Source : Type u} {Target : Type v}
    {original : Span.{u, v, w₁} Source Target}
    {extended : Span.{u, v, w₂} Source Target}
    (extension : CoverageExtension original extended)
    (gap : ExhibitedGap extended) : ExhibitedGap original :=
  ⟨gap.1, fun fiber => gap.2 (extension.liftFiber fiber)⟩

end CoverageExtension

/-- Provenance-bearing repair of one target in a direct span.  The original
    gap is retained, old witnesses embed unchanged, and `addedWitness` names
    the route now discharging that exact target. -/
structure ExactTargetRepair
    {Source : Type u} {Target : Type v}
    (original : Span.{u, v, w₁} Source Target)
    (extended : Span.{u, v, w₂} Source Target) where
  originalGap : ExhibitedGap original
  extension : CoverageExtension original extended
  addedWitness : extended.Witness
  reachesTarget : extended.target addedWitness = originalGap.1

namespace ExactTargetRepair

/-- The identified added route constructs coverage of the exact omitted
    target. -/
def repairedFiber
    {Source : Type u} {Target : Type v}
    {original : Span.{u, v, w₁} Source Target}
    {extended : Span.{u, v, w₂} Source Target}
    (repair : ExactTargetRepair original extended) :
    CoveredTarget extended repair.originalGap.1 :=
  ⟨repair.addedWitness, repair.reachesTarget⟩

/-- The route named by a repair cannot have come from an old exact fiber at
    the omitted target. -/
def originalRouteWasAbsent
    {Source : Type u} {Target : Type v}
    {original : Span.{u, v, w₁} Source Target}
    {extended : Span.{u, v, w₂} Source Target}
    (repair : ExactTargetRepair original extended) :
    CoveredTarget original repair.originalGap.1 → Empty :=
  repair.originalGap.2

/-- The witness identified by the repair is genuinely new relative to the
    injective old-route inclusion.  Otherwise it would reconstruct the exact
    original fiber refuted by `originalGap`. -/
def addedWitnessNotFromOriginal
    {Source : Type u} {Target : Type v}
    {original : Span.{u, v, w₁} Source Target}
    {extended : Span.{u, v, w₂} Source Target}
    (repair : ExactTargetRepair original extended)
    (oldWitness : original.Witness) :
    repair.addedWitness = repair.extension.includeWitness oldWitness → Empty := by
  intro allegedOld
  have includedReaches :
      extended.target (repair.extension.includeWitness oldWitness) =
        repair.originalGap.1 :=
    (congrArg extended.target allegedOld.symm).trans repair.reachesTarget
  have oldReaches : original.target oldWitness = repair.originalGap.1 :=
    (repair.extension.target_preserved oldWitness).symm.trans includedReaches
  exact repair.originalGap.2 ⟨oldWitness, oldReaches⟩

end ExactTargetRepair

/-- An exact composite repair extends the upstream crossing and records the
    complete new route reaching the same final target that the original
    composite omitted. -/
structure ExactCompositeRepair
    {Source : Type u} {Middle : Type v} {Target : Type z}
    (first : Span.{u, v, w₁} Source Middle)
    (extendedFirst : Span.{u, v, w₂} Source Middle)
    (second : Span.{v, z, w₃} Middle Target) where
  originalGap : ExhibitedGap (first.compose second)
  extension : CoverageExtension first extendedFirst
  addedRoute : EndToEndFiber extendedFirst second originalGap.1

/-- **Repair sufficiency.**  The provenance-bearing new end-to-end route
    constructs the repaired composite fiber at the exact formerly omitted
    final target. -/
def repaired_composite_fiber
    {Source : Type u} {Middle : Type v} {Target : Type z}
    {first : Span.{u, v, w₁} Source Middle}
    {extendedFirst : Span.{u, v, w₂} Source Middle}
    {second : Span.{v, z, w₃} Middle Target}
    (repair : ExactCompositeRepair first extendedFirst second) :
    Fiber (extendedFirst.compose second).target repair.originalGap.1 :=
  composite_fiber_of_end_to_end_route repair.addedRoute

/-- Composite repair provenance is exact: the upstream witness in the added
    end-to-end route cannot be the inclusion of any old upstream witness.
    Otherwise the original composite gap would already contain that route. -/
def repaired_composite_upstream_witness_is_new
    {Source : Type u} {Middle : Type v} {Target : Type z}
    {first : Span.{u, v, w₁} Source Middle}
    {extendedFirst : Span.{u, v, w₂} Source Middle}
    {second : Span.{v, z, w₃} Middle Target}
    (repair : ExactCompositeRepair first extendedFirst second)
    (oldWitness : first.Witness) :
    repair.addedRoute.firstFiber.preimage =
        repair.extension.includeWitness oldWitness → Empty := by
  intro allegedOld
  have includedStartsAt :
      extendedFirst.target (repair.extension.includeWitness oldWitness) =
        second.source repair.addedRoute.secondWitness :=
    (congrArg extendedFirst.target allegedOld.symm).trans
      repair.addedRoute.firstFiber.mapsTo
  have oldCompatible :
      first.target oldWitness =
        second.source repair.addedRoute.secondWitness :=
    (repair.extension.target_preserved oldWitness).symm.trans includedStartsAt
  exact repair.originalGap.2
    ⟨{ firstWitness := oldWitness
       secondWitness := repair.addedRoute.secondWitness
       compatible := oldCompatible },
      repair.addedRoute.reachesTarget⟩

/-- An outstanding obligation carries no exhibited negative evidence and can
    coexist with an exact covered target. -/
def obligation_can_coexist_with_coverage
    {Source : Type u} {Target : Type v}
    {B : Span.{u, v, w₁} Source Target}
    {target : Target} (covered : CoveredTarget B target) :
    CoverageObligation B target × CoveredTarget B target :=
  ⟨.outstanding, covered⟩

/-- A target-specific exhibited gap defeats any global coverage receipt. -/
def exhibited_gap_prevents_target_coverage
    {Source : Type u} {Target : Type v}
    {B : Span.{u, v, w₁} Source Target}
    (gap : ExhibitedGap B) : TargetCovered B → Empty :=
  fun covered => gap.2 (covered gap.1)

#print axioms downstream_fiber_of_composite_fiber
#print axioms downstream_covered_of_composite_covered
#print axioms downstream_gap_propagates
#print axioms upstream_gap_propagates_conditionally
#print axioms CoverageExtension.liftFiber
#print axioms CoverageExtension.liftCoverage
#print axioms CoverageExtension.restrictGap
#print axioms ExactTargetRepair.repairedFiber
#print axioms ExactTargetRepair.originalRouteWasAbsent
#print axioms ExactTargetRepair.addedWitnessNotFromOriginal
#print axioms repaired_composite_fiber
#print axioms repaired_composite_upstream_witness_is_new
#print axioms obligation_can_coexist_with_coverage
#print axioms exhibited_gap_prevents_target_coverage

end LeanProofs.GovernedTransport
