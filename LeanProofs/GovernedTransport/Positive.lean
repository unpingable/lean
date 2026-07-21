/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: STABLE-SURFACE

  Positive transport keeps source lifting, translation, and target-local
  reliance as three independent obligations.
-/

import LeanProofs.GovernedTransport.Core

namespace LeanProofs.GovernedTransport

universe u v w p q r

/-- **Licensed positive translation.**  A source realization yields a
    translated target artifact only after the exact presented certificate
    supplies a crossing lift. -/
def translated_realization_of_certificate_lift
    {Source : Type u} {Target : Type v}
    {B : Span.{u, v, w} Source Target}
    {SourcePositive : Source → Type p}
    {TranslatedPositive : Target → Type q}
    (lift : CertificateLift B SourcePositive)
    (translate : TranslateAlong B SourcePositive TranslatedPositive)
    (realized : Realized Source SourcePositive) :
    Realized Target TranslatedPositive := by
  obtain ⟨source, positive⟩ := realized
  obtain ⟨crossing, source_eq⟩ := lift source positive
  refine ⟨B.target crossing, translate crossing ?_⟩
  exact source_eq.symm ▸ positive

/-- Target-local reliance is a second transition after translation.  The
    crossing itself does not authorize it. -/
def relied_realization_of_translated
    {Target : Type v}
    {TranslatedPositive : Target → Type q}
    {TargetPositive : Target → Type r}
    (rely : RelyLocally TranslatedPositive TargetPositive)
    (translated : Realized Target TranslatedPositive) :
    Realized Target TargetPositive :=
  ⟨translated.1, rely translated.1 translated.2⟩

/-- The complete positive path composes licensed lifting, translation, and a
    separately supplied target-local reliance rule. -/
def realized_transport_of_certificate_lift
    {Source : Type u} {Target : Type v}
    {B : Span.{u, v, w} Source Target}
    {SourcePositive : Source → Type p}
    {TranslatedPositive : Target → Type q}
    {TargetPositive : Target → Type r}
    (lift : CertificateLift B SourcePositive)
    (translate : TranslateAlong B SourcePositive TranslatedPositive)
    (rely : RelyLocally TranslatedPositive TargetPositive)
    (realized : Realized Source SourcePositive) :
    Realized Target TargetPositive :=
  relied_realization_of_translated rely
    (translated_realization_of_certificate_lift lift translate realized)

/-- Candidate totality is sufficient but not required for positive
    transport.  The theorem makes the strengthening explicit. -/
def realized_transport_of_candidate_lift
    {Source : Type u} {Target : Type v}
    {B : Span.{u, v, w} Source Target}
    {SourcePositive : Source → Type p}
    {TranslatedPositive : Target → Type q}
    (lift : CandidateLift B)
    (translate : TranslateAlong B SourcePositive TranslatedPositive)
    (realized : Realized Source SourcePositive) :
    Realized Target TranslatedPositive :=
  translated_realization_of_certificate_lift
    (certificate_lift_of_candidate_lift lift) translate realized

#print axioms translated_realization_of_certificate_lift
#print axioms relied_realization_of_translated
#print axioms realized_transport_of_certificate_lift
#print axioms realized_transport_of_candidate_lift

end LeanProofs.GovernedTransport
