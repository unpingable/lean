/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: STABLE-SURFACE

  Minimal reusable vocabulary for governed transport.  A `Span` records only
  proof-relevant crossing geometry.  Translation and target-local reliance
  remain separate laws, and neither is stored in the span itself.

  This module imports nothing and deliberately admits empty, partial, and
  hostile crossing geometries.
-/

namespace LeanProofs.GovernedTransport

universe u v w p q r

/-- Import-free exact equivalence used by the finite specimens. -/
structure ExactEquiv (α : Type u) (β : Type v) where
  toFun : α → β
  invFun : β → α
  left_inv : (value : α) → invFun (toFun value) = value
  right_inv : (value : β) → toFun (invFun value) = value

/-- Bare proof-relevant crossing geometry.  It carries no preservation or
    authority law by construction. -/
structure Span (Source : Type u) (Target : Type v) where
  Witness : Type w
  source : Witness → Source
  target : Witness → Target

/-- Exact proof-relevant membership in the image of a map. -/
structure Fiber {α : Type u} {β : Type v} (f : α → β) (y : β) where
  preimage : α
  mapsTo : f preimage = y

/-- One positively realized candidate and its exact certificate. -/
def Realized (Candidate : Type u) (Positive : Candidate → Type p) :
    Type (max u p) :=
  Σ candidate : Candidate, Positive candidate

/-- A proof-relevant negative certificate for every candidate in the exact
    declared candidate space. -/
def GlobalBlocked (Candidate : Type u) (Negative : Candidate → Type p) :
    Type (max u p) :=
  (candidate : Candidate) → Negative candidate

/-- Candidate-level source totality.  This is stronger than many positive
    transports need because it ignores the certificate being presented. -/
def CandidateLift {Source : Type u} {Target : Type v}
    (B : Span.{u, v, w} Source Target) : Type (max u w) :=
  (source : Source) → Fiber B.source source

/-- Certificate-dependent source lifting.  Transit may be licensed for one
    certificate at a candidate and refused for another certificate at the
    same candidate. -/
def CertificateLift {Source : Type u} {Target : Type v}
    (B : Span.{u, v, w} Source Target) (Positive : Source → Type p) :
    Type (max u w p) :=
  (source : Source) → Positive source → Fiber B.source source

/-- Candidate totality supplies certificate-dependent lifting, but the
    converse is intentionally not claimed. -/
def certificate_lift_of_candidate_lift
    {Source : Type u} {Target : Type v}
    {B : Span.{u, v, w} Source Target}
    {Positive : Source → Type p}
    (lift : CandidateLift B) : CertificateLift B Positive :=
  fun source _ => lift source

/-- Translate a source artifact along an exact crossing witness.  The output
    is a target-indexed artifact, not yet permission for the target to rely on
    it as a local judgment. -/
def TranslateAlong {Source : Type u} {Target : Type v}
    (B : Span.{u, v, w} Source Target)
    (SourceArtifact : Source → Type p)
    (TranslatedArtifact : Target → Type q) : Type (max w p q) :=
  (crossing : B.Witness) →
    SourceArtifact (B.source crossing) →
    TranslatedArtifact (B.target crossing)

/-- A separately owned target-local reliance rule.  Transport can produce an
    artifact without authorizing this step. -/
def RelyLocally {Target : Type v}
    (ImportedArtifact : Target → Type q)
    (TargetJudgment : Target → Type r) : Type (max v q r) :=
  (target : Target) → ImportedArtifact target → TargetJudgment target

/-- Candidate-level and certificate-dependent lift are intentionally
    distinct types even though candidate totality can fund the latter. -/
def candidate_lift_funds_every_certificate
    {Source : Type u} {Target : Type v}
    {B : Span.{u, v, w} Source Target}
    {Positive : Source → Type p}
    (lift : CandidateLift B) (source : Source) (positive : Positive source) :
    Fiber B.source source :=
  certificate_lift_of_candidate_lift lift source positive

#print axioms certificate_lift_of_candidate_lift
#print axioms candidate_lift_funds_every_certificate

end LeanProofs.GovernedTransport
