/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: STABLE-SURFACE

  Tagged federation retains local jurisdiction.  Positive realization is a
  tagged local realization; federation-global blockage is one complete local
  negative certificate for every tag.
-/

import LeanProofs.GovernedTransport.Core

namespace LeanProofs.GovernedTransport

universe i u p q

/-- The faithful heterogeneous federation candidate space. -/
def FederationCandidate (Index : Type i) (Candidate : Index → Type u) :
    Type (max i u) :=
  Σ index : Index, Candidate index

def FederatedPositive
    {Index : Type i} {Candidate : Index → Type u}
    (Positive : (index : Index) → Candidate index → Type p) :
    FederationCandidate Index Candidate → Type p
  | ⟨index, candidate⟩ => Positive index candidate

def FederatedNegative
    {Index : Type i} {Candidate : Index → Type u}
    (Negative : (index : Index) → Candidate index → Type q) :
    FederationCandidate Index Candidate → Type q
  | ⟨index, candidate⟩ => Negative index candidate

/-- A federation realization is exactly one tagged local realization. -/
def federation_realized_equiv
    {Index : Type i} {Candidate : Index → Type u}
    {Positive : (index : Index) → Candidate index → Type p} :
    ExactEquiv
      (Realized (FederationCandidate Index Candidate)
        (FederatedPositive Positive))
      (Σ index : Index, Realized (Candidate index) (Positive index)) where
  toFun realized :=
    ⟨realized.1.1, ⟨realized.1.2, realized.2⟩⟩
  invFun localRealization :=
    ⟨⟨localRealization.1, localRealization.2.1⟩,
      localRealization.2.2⟩
  left_inv realized := by
    cases realized with
    | mk candidate positive =>
        cases candidate
        rfl
  right_inv localRealization := by
    cases localRealization with
    | mk index realized =>
        cases realized
        rfl

/-- Extract the local certificate for one exact jurisdiction from a
    federation-global negative certificate. -/
def federation_global_blocked_to_locals
    {Index : Type i} {Candidate : Index → Type u}
    {Negative : (index : Index) → Candidate index → Type q}
    (blocked : GlobalBlocked (FederationCandidate Index Candidate)
      (FederatedNegative Negative)) :
    (index : Index) → GlobalBlocked (Candidate index) (Negative index) :=
  fun index candidate => blocked ⟨index, candidate⟩

/-- Assemble all tagged local certificates without erasing jurisdiction. -/
def federation_global_blocked_of_all_locals
    {Index : Type i} {Candidate : Index → Type u}
    {Negative : (index : Index) → Candidate index → Type q}
    (blocked : (index : Index) →
      GlobalBlocked (Candidate index) (Negative index)) :
    GlobalBlocked (FederationCandidate Index Candidate)
      (FederatedNegative Negative)
  | ⟨index, candidate⟩ => blocked index candidate

theorem federation_global_round_trip_pointwise
    {Index : Type i} {Candidate : Index → Type u}
    {Negative : (index : Index) → Candidate index → Type q}
    (blocked : GlobalBlocked (FederationCandidate Index Candidate)
      (FederatedNegative Negative))
    (candidate : FederationCandidate Index Candidate) :
    federation_global_blocked_of_all_locals
      (federation_global_blocked_to_locals blocked) candidate =
        blocked candidate := by
  cases candidate
  rfl

theorem federation_local_round_trip_pointwise
    {Index : Type i} {Candidate : Index → Type u}
    {Negative : (index : Index) → Candidate index → Type q}
    (blocked : (index : Index) →
      GlobalBlocked (Candidate index) (Negative index))
    (index : Index) (candidate : Candidate index) :
    federation_global_blocked_to_locals
      (federation_global_blocked_of_all_locals blocked) index candidate =
        blocked index candidate := rfl

/-- Exact dependent-product correspondence for federation-global negative
    evidence.  The function equalities account for the declared `Quot.sound`
    footprint rather than hidden choice. -/
def federation_global_blocked_equiv
    {Index : Type i} {Candidate : Index → Type u}
    {Negative : (index : Index) → Candidate index → Type q} :
    ExactEquiv
      (GlobalBlocked (FederationCandidate Index Candidate)
        (FederatedNegative Negative))
      ((index : Index) → GlobalBlocked (Candidate index) (Negative index)) where
  toFun := federation_global_blocked_to_locals
  invFun := federation_global_blocked_of_all_locals
  left_inv blocked := by
    funext candidate
    exact federation_global_round_trip_pointwise blocked candidate
  right_inv blocked := by
    funext index candidate
    exact federation_local_round_trip_pointwise blocked index candidate

/-- Jurisdiction-retaining inclusion of one local candidate family. -/
def localInclusion
    {Index : Type i} {Candidate : Index → Type u}
    (index : Index) :
    Span (Candidate index) (FederationCandidate Index Candidate) where
  Witness := Candidate index
  source candidate := candidate
  target candidate := ⟨index, candidate⟩

#print axioms federation_realized_equiv
#print axioms federation_global_blocked_to_locals
#print axioms federation_global_blocked_of_all_locals
#print axioms federation_global_round_trip_pointwise
#print axioms federation_local_round_trip_pointwise
#print axioms federation_global_blocked_equiv

end LeanProofs.GovernedTransport
