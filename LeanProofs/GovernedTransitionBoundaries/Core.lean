/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE
  Private-Source-Repository: unpingable/skunkworks
  Private-Source-Commit: b3d73a7a8f3c47486a29767b8b28c809af0f4e57
  Extracted-Tree: 84f209f57e2495463833137cd58aac7ce73e6f96
  Private-Extracted-Source: formalization/PromotionCandidates/V16GovernedTransitionBoundaries/Extracted/LeanProofs/GovernedTransitionBoundaries/Core.lean
  Public-Destination: LeanProofs/GovernedTransitionBoundaries/Core.lean
  Crossing-Campaign-Date: 2026-07-26
  Theorem-Surface: GENERIC-EXPLICIT-FACTORIZATION-CORE
-/

/-
  Generic decoder-factorization boundary for selected semantic targets.

  This public-shaped source remains in private extraction custody.  It uses
  only the existing public fibre-determination vocabulary and does not import
  any private campaign module.
-/

import LeanProofs.ViewSemantics.Core

namespace LeanProofs.GovernedTransitionBoundaries

universe uX uO uP uV

/-- `target` explicitly factors through `observe` when one total deterministic
    decoder works uniformly for every source. -/
def ExplicitlyFactorsThrough
    {X : Type uX} {O : Type uO} {V : Type uV}
    (observe : X → O) (target : X → V) : Prop :=
  ∃ decode : O → V, ∀ source, decode (observe source) = target source

/-- The carrier is obtained solely by deterministic postprocessing of the
    named coarse view; it contributes no independent coordinate. -/
abbrev DerivedOnlyFrom
    {X : Type uX} {O : Type uO} {P : Type uP}
    (coarse : X → O) (carrier : X → P) : Prop :=
  ExplicitlyFactorsThrough coarse carrier

/-- Explicit uniform factorizations compose. -/
theorem explicitFactorization_compose
    {X : Type uX} {O : Type uO} {P : Type uP} {V : Type uV}
    {first : X → O} {middle : X → P} {target : X → V}
    (firstMiddle : ExplicitlyFactorsThrough first middle)
    (middleTarget : ExplicitlyFactorsThrough middle target) :
    ExplicitlyFactorsThrough first target := by
  rcases firstMiddle with ⟨decodeMiddle, middleCorrect⟩
  rcases middleTarget with ⟨decodeTarget, targetCorrect⟩
  refine ⟨fun observation => decodeTarget (decodeMiddle observation), ?_⟩
  intro source
  change decodeTarget (decodeMiddle (first source)) = target source
  rw [middleCorrect, targetCorrect]

/-- An explicit decoder implies the existing public fibre-determination
    relation.  No converse is asserted. -/
theorem explicitFactorization_implies_determines
    {X : Type uX} {O : Type uO} {V : Type uV}
    {observe : X → O} {target : X → V}
    (factors : ExplicitlyFactorsThrough observe target) :
    LeanProofs.ViewSemantics.Determines observe target := by
  rcases factors with ⟨decode, correct⟩
  intro left right sameObservation
  calc
    target left = decode (observe left) := (correct left).symm
    _ = decode (observe right) := congrArg decode sameObservation
    _ = target right := correct right

/-- A target-distinguishing collision blocks an explicit uniform decoder. -/
theorem target_collision_blocks_explicit_factorization
    {X : Type uX} {O : Type uO} {V : Type uV}
    {observe : X → O} {target : X → V} {left right : X}
    (collision : observe left = observe right)
    (separation : target left ≠ target right) :
    ¬ ExplicitlyFactorsThrough observe target := by
  intro factors
  rcases factors with ⟨decode, correct⟩
  apply separation
  calc
    target left = decode (observe left) := (correct left).symm
    _ = decode (observe right) := congrArg decode collision
    _ = target right := correct right

/-- Deterministic postprocessing of an insufficient coarse view cannot restore
    an explicit uniform factorization of the selected target. -/
theorem derived_view_cannot_restore_target
    {X : Type uX} {O : Type uO} {P : Type uP} {V : Type uV}
    {coarse : X → O} {carrier : X → P} {target : X → V}
    (coarseCannotFactor : ¬ ExplicitlyFactorsThrough coarse target)
    (derived : DerivedOnlyFrom coarse carrier) :
    ¬ ExplicitlyFactorsThrough carrier target := by
  intro carrierFactors
  exact coarseCannotFactor
    (explicitFactorization_compose derived carrierFactors)

#print axioms explicitFactorization_compose
#print axioms explicitFactorization_implies_determines
#print axioms target_collision_blocks_explicit_factorization
#print axioms derived_view_cannot_restore_target

end LeanProofs.GovernedTransitionBoundaries
