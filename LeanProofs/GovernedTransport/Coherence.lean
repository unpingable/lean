/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: STABLE-SURFACE

  Explicit coherence for proof-relevant governed crossings.  Bridges are
  compared by witness equivalence together with preservation of both legs;
  endpoint equality and definitional reassociation are deliberately not used
  as substitutes for this receipt.
-/

import LeanProofs.GovernedTransport.Composition
import LeanProofs.GovernedTransport.Identity

namespace LeanProofs.GovernedTransport

universe u v z t w₁ w₂ w₃ p q

/-- Exact equivalence of spans with fixed governed endpoints.  Witnesses may
    have different types, but their source and target legs must agree under
    the explicit witness correspondence. -/
structure LegPreservingSpanEquiv
    {Source : Type u} {Target : Type v}
    (left : Span.{u, v, w₁} Source Target)
    (right : Span.{u, v, w₂} Source Target) where
  witnessEquiv : ExactEquiv left.Witness right.Witness
  source_preserved : (witness : left.Witness) →
    left.source witness = right.source (witnessEquiv.toFun witness)
  target_preserved : (witness : left.Witness) →
    left.target witness = right.target (witnessEquiv.toFun witness)

namespace LegPreservingSpanEquiv

/-- A fiber is determined by its proof-relevant preimage; its equality proof
    is proposition-valued and carries no additional route identity. -/
theorem fiber_eq_of_preimage_eq
    {Domain : Type u} {Codomain : Type v}
    {map : Domain → Codomain} {value : Codomain}
    (left right : Fiber map value)
    (preimageEq : left.preimage = right.preimage) : left = right := by
  cases left with
  | mk leftPreimage leftMapsTo =>
      cases right with
      | mk rightPreimage rightMapsTo =>
          cases preimageEq
          rfl

/-- Reverse an exact leg-preserving span equivalence. -/
def symm
    {Source : Type u} {Target : Type v}
    {left : Span.{u, v, w₁} Source Target}
    {right : Span.{u, v, w₂} Source Target}
    (equiv : LegPreservingSpanEquiv left right) :
    LegPreservingSpanEquiv right left where
  witnessEquiv :=
    { toFun := equiv.witnessEquiv.invFun
      invFun := equiv.witnessEquiv.toFun
      left_inv := equiv.witnessEquiv.right_inv
      right_inv := equiv.witnessEquiv.left_inv }
  source_preserved witness := by
    have preserved :=
      equiv.source_preserved (equiv.witnessEquiv.invFun witness)
    have roundTrip := equiv.witnessEquiv.right_inv witness
    exact (preserved.trans (congrArg right.source roundTrip)).symm
  target_preserved witness := by
    have preserved :=
      equiv.target_preserved (equiv.witnessEquiv.invFun witness)
    have roundTrip := equiv.witnessEquiv.right_inv witness
    exact (preserved.trans (congrArg right.target roundTrip)).symm

/-- Transport an exact source-leg fiber along the witness equivalence. -/
def sourceFiberTo
    {Source : Type u} {Target : Type v}
    {left : Span.{u, v, w₁} Source Target}
    {right : Span.{u, v, w₂} Source Target}
    (equiv : LegPreservingSpanEquiv left right)
    {source : Source} (fiber : Fiber left.source source) :
    Fiber right.source source :=
  ⟨equiv.witnessEquiv.toFun fiber.preimage,
    (equiv.source_preserved fiber.preimage).symm.trans fiber.mapsTo⟩

/-- Transport an exact target-leg fiber along the witness equivalence. -/
def targetFiberTo
    {Source : Type u} {Target : Type v}
    {left : Span.{u, v, w₁} Source Target}
    {right : Span.{u, v, w₂} Source Target}
    (equiv : LegPreservingSpanEquiv left right)
    {target : Target} (fiber : Fiber left.target target) :
    Fiber right.target target :=
  ⟨equiv.witnessEquiv.toFun fiber.preimage,
    (equiv.target_preserved fiber.preimage).symm.trans fiber.mapsTo⟩

/-- Exact source fibers correspond in both directions. -/
def sourceFiberEquiv
    {Source : Type u} {Target : Type v}
    {left : Span.{u, v, w₁} Source Target}
    {right : Span.{u, v, w₂} Source Target}
    (equiv : LegPreservingSpanEquiv left right) (source : Source) :
    ExactEquiv (Fiber left.source source) (Fiber right.source source) where
  toFun := equiv.sourceFiberTo
  invFun := equiv.symm.sourceFiberTo
  left_inv fiber :=
    fiber_eq_of_preimage_eq _ _
      (equiv.witnessEquiv.left_inv fiber.preimage)
  right_inv fiber :=
    fiber_eq_of_preimage_eq _ _
      (equiv.witnessEquiv.right_inv fiber.preimage)

/-- Exact target fibers correspond in both directions. -/
def targetFiberEquiv
    {Source : Type u} {Target : Type v}
    {left : Span.{u, v, w₁} Source Target}
    {right : Span.{u, v, w₂} Source Target}
    (equiv : LegPreservingSpanEquiv left right) (target : Target) :
    ExactEquiv (Fiber left.target target) (Fiber right.target target) where
  toFun := equiv.targetFiberTo
  invFun := equiv.symm.targetFiberTo
  left_inv fiber :=
    fiber_eq_of_preimage_eq _ _
      (equiv.witnessEquiv.left_inv fiber.preimage)
  right_inv fiber :=
    fiber_eq_of_preimage_eq _ _
      (equiv.witnessEquiv.right_inv fiber.preimage)

/-- Proof-relevant target coverage transfers exactly across a leg-preserving
    span equivalence.  Function extensionality records that the pointwise
    fiber round trips assemble into one coverage receipt. -/
def targetCoverageEquiv
    {Source : Type u} {Target : Type v}
    {left : Span.{u, v, w₁} Source Target}
    {right : Span.{u, v, w₂} Source Target}
    (equiv : LegPreservingSpanEquiv left right) :
    ExactEquiv (TargetCovered left) (TargetCovered right) where
  toFun := fun coverage target =>
    (equiv.targetFiberEquiv target).toFun (coverage target)
  invFun := fun coverage target =>
    (equiv.targetFiberEquiv target).invFun (coverage target)
  left_inv coverage := by
    funext target
    exact (equiv.targetFiberEquiv target).left_inv (coverage target)
  right_inv coverage := by
    funext target
    exact (equiv.targetFiberEquiv target).right_inv (coverage target)

/-- An exhibited target gap transfers constructively: any alleged right-hand
    fiber maps back to the exact left-hand fiber refuted by the original gap.
    This does not manufacture a gap from the absence of a coverage receipt. -/
def exhibitedGapTo
    {Source : Type u} {Target : Type v}
    {left : Span.{u, v, w₁} Source Target}
    {right : Span.{u, v, w₂} Source Target}
    (equiv : LegPreservingSpanEquiv left right)
    (gap : ExhibitedGap left) : ExhibitedGap right := by
  obtain ⟨target, unreachable⟩ := gap
  exact ⟨target, fun alleged =>
    unreachable ((equiv.targetFiberEquiv target).invFun alleged)⟩

/-- Exhibited-gap compatibility is bidirectional under exact leg-preserving
    span equivalence. -/
def exhibitedGapFrom
    {Source : Type u} {Target : Type v}
    {left : Span.{u, v, w₁} Source Target}
    {right : Span.{u, v, w₂} Source Target}
    (equiv : LegPreservingSpanEquiv left right)
    (gap : ExhibitedGap right) : ExhibitedGap left :=
  equiv.symm.exhibitedGapTo gap

/-- Candidate lifting is preserved by exact source-fiber correspondence. -/
def candidateLiftTo
    {Source : Type u} {Target : Type v}
    {left : Span.{u, v, w₁} Source Target}
    {right : Span.{u, v, w₂} Source Target}
    (equiv : LegPreservingSpanEquiv left right)
    (lift : CandidateLift left) : CandidateLift right :=
  fun source => (equiv.sourceFiberEquiv source).toFun (lift source)

/-- Certificate-dependent positive lifting is preserved without erasing the
    presented positive certificate. -/
def certificateLiftTo
    {Source : Type u} {Target : Type v}
    {left : Span.{u, v, w₁} Source Target}
    {right : Span.{u, v, w₂} Source Target}
    {Positive : Source → Type p}
    (equiv : LegPreservingSpanEquiv left right)
    (lift : CertificateLift left Positive) : CertificateLift right Positive :=
  fun source positive =>
    (equiv.sourceFiberEquiv source).toFun (lift source positive)

/-- Translation laws move along a leg-preserving equivalence.  The casts are
    exactly the recorded source- and target-leg equalities; no endpoint-only
    identification is used. -/
def translateAlongTo
    {Source : Type u} {Target : Type v}
    {left : Span.{u, v, w₁} Source Target}
    {right : Span.{u, v, w₂} Source Target}
    {SourceArtifact : Source → Type p}
    {TargetArtifact : Target → Type q}
    (equiv : LegPreservingSpanEquiv left right)
    (translate : TranslateAlong left SourceArtifact TargetArtifact) :
    TranslateAlong right SourceArtifact TargetArtifact := by
  intro rightWitness sourceArtifact
  let leftWitness := equiv.witnessEquiv.invFun rightWitness
  have witnessRoundTrip :
      equiv.witnessEquiv.toFun leftWitness = rightWitness :=
    equiv.witnessEquiv.right_inv rightWitness
  have sourceEq : left.source leftWitness = right.source rightWitness :=
    (equiv.source_preserved leftWitness).trans
      (congrArg right.source witnessRoundTrip)
  have targetEq : left.target leftWitness = right.target rightWitness :=
    (equiv.target_preserved leftWitness).trans
      (congrArg right.target witnessRoundTrip)
  exact targetEq ▸ translate leftWitness (sourceEq.symm ▸ sourceArtifact)

/-- Translation compatibility is bidirectional. -/
def translateAlongFrom
    {Source : Type u} {Target : Type v}
    {left : Span.{u, v, w₁} Source Target}
    {right : Span.{u, v, w₂} Source Target}
    {SourceArtifact : Source → Type p}
    {TargetArtifact : Target → Type q}
    (equiv : LegPreservingSpanEquiv left right)
    (translate : TranslateAlong right SourceArtifact TargetArtifact) :
    TranslateAlong left SourceArtifact TargetArtifact :=
  equiv.symm.translateAlongTo translate

/-- Image-relative negative evidence transfers without being promoted to
    target-global evidence. -/
def blockedAlongTo
    {Source : Type u} {Target : Type v}
    {left : Span.{u, v, w₁} Source Target}
    {right : Span.{u, v, w₂} Source Target}
    {Negative : Target → Type p}
    (equiv : LegPreservingSpanEquiv left right)
    (blocked : BlockedAlong left Negative) : BlockedAlong right Negative := by
  intro rightWitness
  let leftWitness := equiv.witnessEquiv.invFun rightWitness
  have witnessRoundTrip :
      equiv.witnessEquiv.toFun leftWitness = rightWitness :=
    equiv.witnessEquiv.right_inv rightWitness
  have targetEq : left.target leftWitness = right.target rightWitness :=
    (equiv.target_preserved leftWitness).trans
      (congrArg right.target witnessRoundTrip)
  exact targetEq ▸ blocked leftWitness

/-- Image-relative negative compatibility is bidirectional. -/
def blockedAlongFrom
    {Source : Type u} {Target : Type v}
    {left : Span.{u, v, w₁} Source Target}
    {right : Span.{u, v, w₂} Source Target}
    {Negative : Target → Type p}
    (equiv : LegPreservingSpanEquiv left right)
    (blocked : BlockedAlong right Negative) : BlockedAlong left Negative :=
  equiv.symm.blockedAlongTo blocked

end LegPreservingSpanEquiv

/-! ## Identity coherence -/

/-- Explicit left-unit witness correspondence. -/
def compose_identity_left_witness_equiv
    {Source : Type u} {Target : Type v}
    (bridge : Span.{u, v, w₁} Source Target) :
    ExactEquiv ((identitySpan Source).compose bridge).Witness bridge.Witness where
  toFun := fun crossing => crossing.secondWitness
  invFun := fun witness =>
    { firstWitness := ⟨bridge.source witness⟩
      secondWitness := witness
      compatible := rfl }
  left_inv crossing := by
    cases crossing with
    | mk identityWitness witness compatible =>
        cases identityWitness with
        | mk candidate =>
            cases compatible
            rfl
  right_inv _ := rfl

/-- Composing an identity crossing on the left preserves the original bridge
    through witness and leg equivalence. -/
def compose_identity_left_equiv
    {Source : Type u} {Target : Type v}
    (bridge : Span.{u, v, w₁} Source Target) :
    LegPreservingSpanEquiv ((identitySpan Source).compose bridge) bridge where
  witnessEquiv := compose_identity_left_witness_equiv bridge
  source_preserved crossing := crossing.compatible
  target_preserved _ := rfl

/-- Explicit right-unit witness correspondence. -/
def compose_identity_right_witness_equiv
    {Source : Type u} {Target : Type v}
    (bridge : Span.{u, v, w₁} Source Target) :
    ExactEquiv (bridge.compose (identitySpan Target)).Witness bridge.Witness where
  toFun := fun crossing => crossing.firstWitness
  invFun := fun witness =>
    { firstWitness := witness
      secondWitness := ⟨bridge.target witness⟩
      compatible := rfl }
  left_inv crossing := by
    cases crossing with
    | mk witness identityWitness compatible =>
        cases identityWitness with
        | mk candidate =>
            cases compatible
            rfl
  right_inv _ := rfl

/-- Composing an identity crossing on the right preserves the original bridge
    through witness and leg equivalence. -/
def compose_identity_right_equiv
    {Source : Type u} {Target : Type v}
    (bridge : Span.{u, v, w₁} Source Target) :
    LegPreservingSpanEquiv (bridge.compose (identitySpan Target)) bridge where
  witnessEquiv := compose_identity_right_witness_equiv bridge
  source_preserved _ := rfl
  target_preserved crossing := crossing.compatible.symm

/-! ## Associativity coherence -/

/-- Reassociate the nested proof-relevant pullback witness explicitly. -/
def compose_associator_witness_equiv
    {A : Type u} {B : Type v} {C : Type z} {D : Type t}
    (first : Span.{u, v, w₁} A B)
    (second : Span.{v, z, w₂} B C)
    (third : Span.{z, t, w₃} C D) :
    ExactEquiv ((first.compose second).compose third).Witness
      (first.compose (second.compose third)).Witness where
  toFun := fun crossing =>
    { firstWitness := crossing.firstWitness.firstWitness
      secondWitness :=
        { firstWitness := crossing.firstWitness.secondWitness
          secondWitness := crossing.secondWitness
          compatible := crossing.compatible }
      compatible := crossing.firstWitness.compatible }
  invFun := fun crossing =>
    { firstWitness :=
        { firstWitness := crossing.firstWitness
          secondWitness := crossing.secondWitness.firstWitness
          compatible := crossing.compatible }
      secondWitness := crossing.secondWitness.secondWitness
      compatible := crossing.secondWitness.compatible }
  left_inv crossing := by
    cases crossing with
    | mk firstSecondWitness thirdWitness secondThirdCompatible =>
        cases firstSecondWitness
        rfl
  right_inv crossing := by
    cases crossing with
    | mk firstWitness secondThirdWitness firstSecondCompatible =>
        cases secondThirdWitness
        rfl

/-- Composition is associative through an explicit equivalence of nested
    pullback witnesses.  It is not asserted as structure equality. -/
def compose_associator_equiv
    {A : Type u} {B : Type v} {C : Type z} {D : Type t}
    (first : Span.{u, v, w₁} A B)
    (second : Span.{v, z, w₂} B C)
    (third : Span.{z, t, w₃} C D) :
    LegPreservingSpanEquiv
      ((first.compose second).compose third)
      (first.compose (second.compose third)) where
  witnessEquiv := compose_associator_witness_equiv first second third
  source_preserved _ := rfl
  target_preserved _ := rfl

/-- Exact final fibers transfer across explicit associativity coherence. -/
def associator_target_fiber_equiv
    {A : Type u} {B : Type v} {C : Type z} {D : Type t}
    {first : Span.{u, v, w₁} A B}
    {second : Span.{v, z, w₂} B C}
    {third : Span.{z, t, w₃} C D}
    (target : D) :
    ExactEquiv
      (Fiber ((first.compose second).compose third).target target)
      (Fiber (first.compose (second.compose third)).target target) :=
  (compose_associator_equiv first second third).targetFiberEquiv target

/-- Proof-relevant final-target coverage transfers across the associator. -/
def associator_target_coverage_equiv
    {A : Type u} {B : Type v} {C : Type z} {D : Type t}
    {first : Span.{u, v, w₁} A B}
    {second : Span.{v, z, w₂} B C}
    {third : Span.{z, t, w₃} C D} :
    ExactEquiv
      (TargetCovered ((first.compose second).compose third))
      (TargetCovered (first.compose (second.compose third))) :=
  (compose_associator_equiv first second third).targetCoverageEquiv

#print axioms LegPreservingSpanEquiv
#print axioms LegPreservingSpanEquiv.fiber_eq_of_preimage_eq
#print axioms LegPreservingSpanEquiv.symm
#print axioms LegPreservingSpanEquiv.sourceFiberTo
#print axioms LegPreservingSpanEquiv.targetFiberTo
#print axioms LegPreservingSpanEquiv.sourceFiberEquiv
#print axioms LegPreservingSpanEquiv.targetFiberEquiv
#print axioms LegPreservingSpanEquiv.targetCoverageEquiv
#print axioms LegPreservingSpanEquiv.exhibitedGapTo
#print axioms LegPreservingSpanEquiv.exhibitedGapFrom
#print axioms LegPreservingSpanEquiv.candidateLiftTo
#print axioms LegPreservingSpanEquiv.certificateLiftTo
#print axioms LegPreservingSpanEquiv.translateAlongTo
#print axioms LegPreservingSpanEquiv.translateAlongFrom
#print axioms LegPreservingSpanEquiv.blockedAlongTo
#print axioms LegPreservingSpanEquiv.blockedAlongFrom
#print axioms compose_identity_left_witness_equiv
#print axioms compose_identity_left_equiv
#print axioms compose_identity_right_witness_equiv
#print axioms compose_identity_right_equiv
#print axioms compose_associator_witness_equiv
#print axioms compose_associator_equiv
#print axioms associator_target_fiber_equiv
#print axioms associator_target_coverage_equiv

end LeanProofs.GovernedTransport
