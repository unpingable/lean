/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: STABLE-SURFACE

  Minimal honest residue for incomplete negative transport.  Coverage debt is
  not semantic refusal, and a total result is available only from an explicit
  coverage decision.
-/

import LeanProofs.GovernedTransport.Negative

namespace LeanProofs.GovernedTransport

universe u v w p q r

/-- A negative transport result is indexed by the exact transported blockage.
    The global branch adds proof-relevant target coverage; the indeterminate
    branch retains outstanding or exhibited coverage debt. -/
inductive NegativeTransportOutcome
    {Source : Type u} {Target : Type v}
    (B : Span.{u, v, w} Source Target)
    {SourceNegative : Source → Type p}
    {ImportedNegative : Target → Type q}
    {TargetNegative : Target → Type r}
    (transported : TransportedBlockage B SourceNegative
      ImportedNegative TargetNegative) : Type (max v w p q r) where
  | indeterminate (debt : CoverageDebt B) :
      NegativeTransportOutcome B transported
  | globalBlocked (coverage : TargetCovered B) :
      NegativeTransportOutcome B transported

/-- Resolve the outcome without confusing an incomplete evaluation with a
    target-global negative certificate. -/
def NegativeTransportOutcome.resolve
    {Source : Type u} {Target : Type v}
    {B : Span.{u, v, w} Source Target}
    {SourceNegative : Source → Type p}
    {ImportedNegative : Target → Type q}
    {TargetNegative : Target → Type r}
    {transported : TransportedBlockage B SourceNegative
      ImportedNegative TargetNegative}
    (outcome : NegativeTransportOutcome B transported) :
    CoverageDebt B ⊕ GlobalBlocked Target TargetNegative :=
  match outcome with
  | .indeterminate debt => .inl debt
  | .globalBlocked coverage => .inr (transported.globalize coverage)

/-- Before a coverage receipt or exact gap is presented, preserve the
    transported image blockage with an outstanding obligation. -/
def negative_transport_with_outstanding_coverage
    {Source : Type u} {Target : Type v}
    {B : Span.{u, v, w} Source Target}
    {SourceNegative : Source → Type p}
    {ImportedNegative : Target → Type q}
    {TargetNegative : Target → Type r}
    (transported : TransportedBlockage B SourceNegative
      ImportedNegative TargetNegative) :
    NegativeTransportOutcome B transported :=
  .indeterminate .outstanding

/-- An exhibited gap refines the debt but still does not create semantic
    refusal at the uncovered target. -/
def negative_transport_with_exhibited_gap
    {Source : Type u} {Target : Type v}
    {B : Span.{u, v, w} Source Target}
    {SourceNegative : Source → Type p}
    {ImportedNegative : Target → Type q}
    {TargetNegative : Target → Type r}
    (transported : TransportedBlockage B SourceNegative
      ImportedNegative TargetNegative)
    (gap : ExhibitedGap B) : NegativeTransportOutcome B transported :=
  .indeterminate (.exhibited gap)

/-- Exact target coverage permits the global branch. -/
def negative_transport_with_target_coverage
    {Source : Type u} {Target : Type v}
    {B : Span.{u, v, w} Source Target}
    {SourceNegative : Source → Type p}
    {ImportedNegative : Target → Type q}
    {TargetNegative : Target → Type r}
    (transported : TransportedBlockage B SourceNegative
      ImportedNegative TargetNegative)
    (coverage : TargetCovered B) : NegativeTransportOutcome B transported :=
  .globalBlocked coverage

/-- An explicit coverage-decision receipt yields a total negative transport
    outcome.  This generic sum is exact witnessed data, not by itself an
    executable procedure; the finite hostile supplies the executable case. -/
def negative_transport_of_coverage_decision
    {Source : Type u} {Target : Type v}
    {B : Span.{u, v, w} Source Target}
    {SourceNegative : Source → Type p}
    {ImportedNegative : Target → Type q}
    {TargetNegative : Target → Type r}
    (transported : TransportedBlockage B SourceNegative
      ImportedNegative TargetNegative)
    (decision : CoverageDecision B) : NegativeTransportOutcome B transported :=
  match decision with
  | .inl coverage => .globalBlocked coverage
  | .inr gap => .indeterminate (.exhibited gap)

#print axioms NegativeTransportOutcome.resolve
#print axioms negative_transport_with_outstanding_coverage
#print axioms negative_transport_with_exhibited_gap
#print axioms negative_transport_with_target_coverage
#print axioms negative_transport_of_coverage_decision

end LeanProofs.GovernedTransport
