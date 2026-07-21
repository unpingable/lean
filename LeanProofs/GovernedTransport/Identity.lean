/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: STABLE-SURFACE

  The minimum faithful identity crossing.  Identity is a proof-relevant
  crossing with one named witness per candidate; equality of endpoint types
  alone does not provide this witness geometry or preserve route-carried
  force.
-/

import LeanProofs.GovernedTransport.Positive
import LeanProofs.GovernedTransport.Negative

namespace LeanProofs.GovernedTransport

universe u p

/-- The witness of an identity crossing records the exact candidate being
    preserved.  Keeping this as a structure makes the crossing witness an
    explicit part of the receipt rather than silently identifying it with an
    endpoint equality. -/
structure IdentityWitness (Candidate : Type u) where
  candidate : Candidate

/-- Proof-relevant identity crossing. -/
def identitySpan (Candidate : Type u) : Span Candidate Candidate where
  Witness := IdentityWitness Candidate
  source witness := witness.candidate
  target witness := witness.candidate

/-- Both legs of the identity witness name its recorded candidate. -/
theorem identity_source_leg
    {Candidate : Type u} (witness : IdentityWitness Candidate) :
    (identitySpan Candidate).source witness = witness.candidate :=
  rfl

/-- Both legs of the identity witness name its recorded candidate. -/
theorem identity_target_leg
    {Candidate : Type u} (witness : IdentityWitness Candidate) :
    (identitySpan Candidate).target witness = witness.candidate :=
  rfl

/-- Every source candidate has its exact identity witness. -/
def identity_candidate_lift {Candidate : Type u} :
    CandidateLift (identitySpan Candidate) :=
  fun candidate => ⟨⟨candidate⟩, rfl⟩

/-- Identity lifting remains certificate-sensitive in type while reusing the
    exact candidate named by the presented certificate. -/
def identity_certificate_lift
    {Candidate : Type u} {Positive : Candidate → Type p} :
    CertificateLift (identitySpan Candidate) Positive :=
  certificate_lift_of_candidate_lift identity_candidate_lift

/-- Identity translation retains the exact presented artifact. -/
def identity_translate
    {Candidate : Type u} {Artifact : Candidate → Type p} :
    TranslateAlong (identitySpan Candidate) Artifact Artifact :=
  fun _ artifact => artifact

/-- The ordinary positive pipeline through the identity crossing. -/
def identity_positive_transport
    {Candidate : Type u} {Positive : Candidate → Type p}
    (realized : Realized Candidate Positive) :
    Realized Candidate Positive :=
  translated_realization_of_certificate_lift
    identity_certificate_lift identity_translate realized

/-- Positive identity transport preserves both the candidate and its
    proof-relevant positive certificate, not merely endpoint membership. -/
theorem identity_positive_transport_eq
    {Candidate : Type u} {Positive : Candidate → Type p}
    (realized : Realized Candidate Positive) :
    identity_positive_transport realized = realized := by
  cases realized
  rfl

/-- Positive identity transport is an exact equivalence whose forward map is
    the governed-transport positive pipeline itself. -/
def identity_positive_equiv
    {Candidate : Type u} {Positive : Candidate → Type p} :
    ExactEquiv (Realized Candidate Positive) (Realized Candidate Positive) where
  toFun := identity_positive_transport
  invFun := fun realized => realized
  left_inv := identity_positive_transport_eq
  right_inv := identity_positive_transport_eq

/-- Package source-global negative evidence for transport across identity. -/
def identity_transported_blockage
    {Candidate : Type u} {Negative : Candidate → Type p}
    (blocked : GlobalBlocked Candidate Negative) :
    TransportedBlockage (identitySpan Candidate) Negative Negative Negative where
  sourceBlocked := blocked
  translate := identity_translate
  rely := fun _ negative => negative

/-- Reconstructed image-relative negative evidence is the exact original
    source evidence at the candidate named by the identity witness. -/
theorem identity_negative_blocked_along_eq
    {Candidate : Type u} {Negative : Candidate → Type p}
    (blocked : GlobalBlocked Candidate Negative) (candidate : Candidate) :
    (identity_transported_blockage blocked).blockedAlong ⟨candidate⟩ =
      blocked candidate :=
  rfl

/-- Identity target coverage is constructive data: it selects the identity
    witness for every target candidate. -/
def identity_target_covered {Candidate : Type u} :
    TargetCovered (identitySpan Candidate) :=
  fun candidate => ⟨⟨candidate⟩, rfl⟩

/-- Globalizing transported negative evidence through exact identity coverage
    preserves the original proof-relevant evidence pointwise. -/
theorem identity_negative_globalization_pointwise
    {Candidate : Type u} {Negative : Candidate → Type p}
    (blocked : GlobalBlocked Candidate Negative) (candidate : Candidate) :
    (identity_transported_blockage blocked).globalize
        identity_target_covered candidate = blocked candidate :=
  rfl

/-- The complete negative pipeline through identity is extensionally the
    original source-global negative witness. -/
theorem identity_negative_globalization_eq
    {Candidate : Type u} {Negative : Candidate → Type p}
    (blocked : GlobalBlocked Candidate Negative) :
    (identity_transported_blockage blocked).globalize
        identity_target_covered = blocked := by
  funext candidate
  exact identity_negative_globalization_pointwise blocked candidate

/-- Negative identity transport is an exact equivalence whose forward map
    performs transported blockage followed by the exact coverage upgrade. -/
def identity_negative_equiv
    {Candidate : Type u} {Negative : Candidate → Type p} :
    ExactEquiv (GlobalBlocked Candidate Negative)
      (GlobalBlocked Candidate Negative) where
  toFun := fun blocked =>
    (identity_transported_blockage blocked).globalize identity_target_covered
  invFun := fun blocked => blocked
  left_inv := identity_negative_globalization_eq
  right_inv := identity_negative_globalization_eq

#print axioms identitySpan
#print axioms identity_source_leg
#print axioms identity_target_leg
#print axioms identity_candidate_lift
#print axioms identity_certificate_lift
#print axioms identity_translate
#print axioms identity_positive_transport
#print axioms identity_positive_transport_eq
#print axioms identity_positive_equiv
#print axioms identity_transported_blockage
#print axioms identity_negative_blocked_along_eq
#print axioms identity_target_covered
#print axioms identity_negative_globalization_pointwise
#print axioms identity_negative_globalization_eq
#print axioms identity_negative_equiv

end LeanProofs.GovernedTransport
