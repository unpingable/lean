/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE

  The minimum faithful identity crossing.  Identity is a proof-relevant
  crossing with one named witness per candidate; equality of endpoint types
  alone does not provide this witness geometry or preserve route-carried
  force.
-/

import LeanProofs.GovernedTransport.Identity

namespace LeanProofs.GovernedTransport

/-! ## Endpoint-equality hostile specimens -/

namespace EndpointEqualityHostile

/-- Equal source and target types do not imply identity coverage.  This span
    has those endpoint types but reaches only `false`. -/
def partialSpan : Span Bool Bool where
  Witness := Unit
  source _ := false
  target _ := false

def trueGap : ExhibitedGap partialSpan := by
  refine ⟨true, ?_⟩
  intro alleged
  exact Bool.noConfusion alleged.mapsTo

/-- Endpoint-type equality cannot manufacture the proof-relevant coverage
    receipt supplied by `identitySpan`. -/
theorem endpoint_equality_does_not_supply_identity_coverage :
    TargetCovered partialSpan → False :=
  fun covered => target_covered_excludes_gap covered trueGap

/-- Even with a single equal endpoint, two crossing witnesses may carry
    observably different force. -/
def parallel : Span Unit Unit where
  Witness := Bool
  source _ := ()
  target _ := ()

def SourceArtifact (_ : Unit) : Type := Unit
def RouteForce (_ : Unit) : Type := Bool

def route_sensitive_translate :
    TranslateAlong parallel SourceArtifact RouteForce :=
  fun route _ => route

def realized : Realized Unit SourceArtifact := ⟨(), ()⟩

def liftFalse : CertificateLift parallel SourceArtifact :=
  fun _ _ => ⟨false, rfl⟩

def liftTrue : CertificateLift parallel SourceArtifact :=
  fun _ _ => ⟨true, rfl⟩

def transportedFalse : Realized Unit RouteForce :=
  translated_realization_of_certificate_lift
    liftFalse route_sensitive_translate realized

def transportedTrue : Realized Unit RouteForce :=
  translated_realization_of_certificate_lift
    liftTrue route_sensitive_translate realized

/-- Equal endpoints do not identify proof-relevant routes or their carried
    evidence.  A faithful identity crossing must fix this witness behavior. -/
theorem endpoint_equality_does_not_preserve_route_force :
    transportedFalse.1 = transportedTrue.1 ∧
      transportedFalse.2 ≠ transportedTrue.2 := by
  exact ⟨rfl, Bool.noConfusion⟩

end EndpointEqualityHostile

#print axioms EndpointEqualityHostile.endpoint_equality_does_not_supply_identity_coverage
#print axioms EndpointEqualityHostile.endpoint_equality_does_not_preserve_route_force

end LeanProofs.GovernedTransport
