/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: STABLE-SURFACE

  Constructive, proof-relevant target coverage.  Lack of a coverage receipt,
  negated coverage, an exhibited gap, and a decidable result remain distinct.
-/

import LeanProofs.GovernedTransport.Core

namespace LeanProofs.GovernedTransport

universe u v w

/-- Coverage is data: each target receives an exact crossing fiber. -/
def TargetCovered {Source : Type u} {Target : Type v}
    (B : Span.{u, v, w} Source Target) : Type (max v w) :=
  (target : Target) → Fiber B.target target

/-- A constructive target outside the bridge image. -/
def ExhibitedGap {Source : Type u} {Target : Type v}
    (B : Span.{u, v, w} Source Target) : Type (max v w) :=
  Σ target : Target, Fiber B.target target → Empty

/-- Honest coverage debt is either still outstanding or refined by an exact
    exhibited gap.  Neither case is a semantic refusal at that target, and
    `outstanding` is not a decision: it may coexist with actual coverage when
    no receipt has yet been presented to this boundary. -/
inductive CoverageDebt {Source : Type u} {Target : Type v}
    (B : Span.{u, v, w} Source Target) : Type (max v w) where
  | outstanding : CoverageDebt B
  | exhibited (gap : ExhibitedGap B) : CoverageDebt B

/-- A coverage decision must return exact positive coverage data or an exact
    exhibited gap.  Merely lacking a proof cannot inhabit this type. -/
def CoverageDecision {Source : Type u} {Target : Type v}
    (B : Span.{u, v, w} Source Target) : Type (max v w) :=
  TargetCovered B ⊕ ExhibitedGap B

/-- A supplied coverage receipt and an exhibited gap are incompatible. -/
theorem target_covered_excludes_gap
    {Source : Type u} {Target : Type v}
    {B : Span.{u, v, w} Source Target}
    (coverage : TargetCovered B) (gap : ExhibitedGap B) : False := by
  obtain ⟨target, unreachable⟩ := gap
  exact (unreachable (coverage target)).elim

/-- Extract the exact target fiber from a positive decision branch. -/
def target_fiber_of_covered_decision
    {Source : Type u} {Target : Type v}
    {B : Span.{u, v, w} Source Target}
    (coverage : TargetCovered B) (target : Target) : Fiber B.target target :=
  coverage target

#print axioms target_covered_excludes_gap
#print axioms target_fiber_of_covered_decision

end LeanProofs.GovernedTransport
