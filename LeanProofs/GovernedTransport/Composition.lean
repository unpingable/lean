/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: STABLE-SURFACE

  Proof-relevant span composition.  Composite coverage is exact end-to-end
  reachability through compatible witnesses, not completeness of the final
  leg considered in isolation.
-/

import LeanProofs.GovernedTransport.Coverage

namespace LeanProofs.GovernedTransport

universe u v z w₁ w₂

/-- A pullback witness is a pair of crossing witnesses plus exact agreement
    at the intermediate candidate. -/
structure PullbackWitness
    {Source : Type u} {Middle : Type v} {Target : Type z}
    (first : Span.{u, v, w₁} Source Middle)
    (second : Span.{v, z, w₂} Middle Target) where
  firstWitness : first.Witness
  secondWitness : second.Witness
  compatible : first.target firstWitness = second.source secondWitness

/-- Compose spans through proof-relevant pullback witnesses. -/
def Span.compose
    {Source : Type u} {Middle : Type v} {Target : Type z}
    (first : Span.{u, v, w₁} Source Middle)
    (second : Span.{v, z, w₂} Middle Target) : Span Source Target where
  Witness := PullbackWitness first second
  source crossing := first.source crossing.firstWitness
  target crossing := second.target crossing.secondWitness

/-- Exact end-to-end evidence reaching one final target. -/
structure EndToEndFiber
    {Source : Type u} {Middle : Type v} {Target : Type z}
    (first : Span.{u, v, w₁} Source Middle)
    (second : Span.{v, z, w₂} Middle Target)
    (target : Target) where
  secondWitness : second.Witness
  firstFiber : Fiber first.target (second.source secondWitness)
  reachesTarget : second.target secondWitness = target

/-- **Exact composite fiber.**  A composite target fiber is equivalent to an
    explicit final-leg witness whose starting candidate has an upstream
    fiber. -/
def composite_fiber_equiv
    {Source : Type u} {Middle : Type v} {Target : Type z}
    {first : Span.{u, v, w₁} Source Middle}
    {second : Span.{v, z, w₂} Middle Target}
    (target : Target) :
    ExactEquiv (Fiber (first.compose second).target target)
      (EndToEndFiber first second target) where
  toFun compositeFiber :=
    { secondWitness := compositeFiber.preimage.secondWitness
      firstFiber :=
        ⟨compositeFiber.preimage.firstWitness,
          compositeFiber.preimage.compatible⟩
      reachesTarget := compositeFiber.mapsTo }
  invFun route :=
    { preimage :=
        { firstWitness := route.firstFiber.preimage
          secondWitness := route.secondWitness
          compatible := route.firstFiber.mapsTo }
      mapsTo := route.reachesTarget }
  left_inv compositeFiber := by
    cases compositeFiber with
    | mk crossing mapsTo =>
        cases crossing
        rfl
  right_inv route := by
    cases route with
    | mk secondWitness firstFiber reachesTarget =>
        cases firstFiber
        rfl

/-- Every downstream witness begins at a candidate actually funded by the
    first bridge.  This is the exact intermediate obligation used below. -/
def IntermediateCovered
    {Source : Type u} {Middle : Type v} {Target : Type z}
    (first : Span.{u, v, w₁} Source Middle)
    (second : Span.{v, z, w₂} Middle Target) : Type (max w₁ w₂) :=
  (secondWitness : second.Witness) →
    Fiber first.target (second.source secondWitness)

/-- Full first-leg target coverage supplies the required intermediate fiber
    for every downstream witness. -/
def intermediate_covered_of_first_target_covered
    {Source : Type u} {Middle : Type v} {Target : Type z}
    {first : Span.{u, v, w₁} Source Middle}
    {second : Span.{v, z, w₂} Middle Target}
    (firstCovered : TargetCovered first) : IntermediateCovered first second :=
  fun secondWitness => firstCovered (second.source secondWitness)

/-- **Constructive composite coverage.**  Each final target is supplied with
    a selected downstream witness and that exact witness is supplied with an
    upstream fiber. -/
def composite_target_covered
    {Source : Type u} {Middle : Type v} {Target : Type z}
    {first : Span.{u, v, w₁} Source Middle}
    {second : Span.{v, z, w₂} Middle Target}
    (intermediateCovered : IntermediateCovered first second)
    (secondCovered : TargetCovered second) :
    TargetCovered (first.compose second) := by
  intro target
  obtain ⟨secondWitness, reachesTarget⟩ := secondCovered target
  obtain ⟨firstWitness, compatible⟩ := intermediateCovered secondWitness
  exact
    ⟨{ firstWitness := firstWitness
       secondWitness := secondWitness
       compatible := compatible },
      reachesTarget⟩

/-- Proof-relevant coverage of both component targets is sufficient for
    proof-relevant composite coverage. -/
def both_leg_coverage_implies_composite_coverage
    {Source : Type u} {Middle : Type v} {Target : Type z}
    {first : Span.{u, v, w₁} Source Middle}
    {second : Span.{v, z, w₂} Middle Target}
    (firstCovered : TargetCovered first)
    (secondCovered : TargetCovered second) :
    TargetCovered (first.compose second) :=
  composite_target_covered
    (intermediate_covered_of_first_target_covered firstCovered)
    secondCovered

/-- Composite coverage is exactly one complete compatible route per final
    target. -/
def composite_coverage_equiv
    {Source : Type u} {Middle : Type v} {Target : Type z}
    {first : Span.{u, v, w₁} Source Middle}
    {second : Span.{v, z, w₂} Middle Target} :
    ExactEquiv (TargetCovered (first.compose second))
      ((target : Target) → EndToEndFiber first second target) where
  toFun covered target :=
    (composite_fiber_equiv target).toFun (covered target)
  invFun routes target :=
    (composite_fiber_equiv target).invFun (routes target)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Any alleged composite coverage of a final target exposes the exact
    upstream fiber funding its selected downstream witness.  This is the
    reusable non-laundering direction used by omission hostiles. -/
def upstream_fiber_of_composite_fiber
    {Source : Type u} {Middle : Type v} {Target : Type z}
    {first : Span.{u, v, w₁} Source Middle}
    {second : Span.{v, z, w₂} Middle Target}
    {target : Target}
    (covered : Fiber (first.compose second).target target) :
    Fiber first.target
      (second.source covered.preimage.secondWitness) :=
  ⟨covered.preimage.firstWitness, covered.preimage.compatible⟩

/-- Adding an exact end-to-end route repairs coverage of precisely the final
    target named by that route. -/
def composite_fiber_of_end_to_end_route
    {Source : Type u} {Middle : Type v} {Target : Type z}
    {first : Span.{u, v, w₁} Source Middle}
    {second : Span.{v, z, w₂} Middle Target}
    {target : Target}
    (route : EndToEndFiber first second target) :
    Fiber (first.compose second).target target :=
  (composite_fiber_equiv target).invFun route

#print axioms composite_fiber_equiv
#print axioms intermediate_covered_of_first_target_covered
#print axioms composite_target_covered
#print axioms both_leg_coverage_implies_composite_coverage
#print axioms composite_coverage_equiv
#print axioms upstream_fiber_of_composite_fiber
#print axioms composite_fiber_of_end_to_end_route

end LeanProofs.GovernedTransport
