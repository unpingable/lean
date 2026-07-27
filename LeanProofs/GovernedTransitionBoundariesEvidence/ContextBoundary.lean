/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE
  Private-Source-Repository: unpingable/skunkworks
  Private-Source-Commit: b3d73a7a8f3c47486a29767b8b28c809af0f4e57
  Extracted-Tree: 84f209f57e2495463833137cd58aac7ce73e6f96
  Private-Extracted-Source: formalization/PromotionCandidates/V16GovernedTransitionBoundaries/Extracted/LeanProofs/GovernedTransitionBoundariesEvidence/ContextBoundary.lean
  Public-Destination: LeanProofs/GovernedTransitionBoundariesEvidence/ContextBoundary.lean
  Crossing-Campaign-Date: 2026-07-26
  Theorem-Surface: SELECTED-CONTEXT-VALIDATION-WITNESS
-/

/-
  One fixed issued observation record evaluated at exactly two selected
  current contexts.
-/

import LeanProofs.GovernedTransitionBoundaries

namespace LeanProofs.GovernedTransitionBoundariesEvidence

open LeanProofs.GovernedTransitionBoundaries

namespace ContextFixture

inductive ObservationUseContext where
  | issuance
  | otherPrefix
  deriving DecidableEq, Repr

inductive PairEvent where
  | left
  deriving DecidableEq, Repr

structure ObservationOperation where
  consumer : Nat
  queriedEvent : PairEvent
  deriving DecidableEq, Repr

structure InstrumentedState where
  leftPresent : Bool
  deriving DecidableEq, Repr

def ObservationAdmitted (operation : ObservationOperation) : Prop :=
  operation.consumer = 41 ∧ operation.queriedEvent = .left

def ObservationPriorValid (prior : InstrumentedState) : Prop :=
  prior.leftPresent = true

structure ApparentObservationContent where
  consumer : Nat
  queriedEvent : PairEvent
  observedPresent : Bool
  deriving DecidableEq, Repr

structure ObservationCertificate where
  id : Nat
  prior : InstrumentedState
  operation : ObservationOperation
  admitted : ObservationAdmitted operation
  validPrior : ObservationPriorValid prior

def ObservationUseContext.state :
    ObservationUseContext → InstrumentedState
  | .issuance => { leftPresent := true }
  | .otherPrefix => { leftPresent := false }

def formingRead : ObservationOperation :=
  { consumer := 41, queriedEvent := .left }

def apparentContentAt
    (state : InstrumentedState) (operation : ObservationOperation) :
    ApparentObservationContent :=
  { consumer := operation.consumer
    queriedEvent := operation.queriedEvent
    observedPresent := state.leftPresent }

def firstCertificate : ObservationCertificate :=
  { id := 1
    prior := ObservationUseContext.state .issuance
    operation := formingRead
    admitted := ⟨rfl, rfl⟩
    validPrior := rfl }

def ObservationCertificate.historicalContent
    (certificate : ObservationCertificate) :
    ApparentObservationContent :=
  apparentContentAt certificate.prior certificate.operation

def issuedObservationView (_ : ObservationUseContext) :
    ObservationCertificate :=
  firstCertificate

def currentObservationValidity
    (context : ObservationUseContext) : Prop :=
  firstCertificate.historicalContent =
    apparentContentAt context.state firstCertificate.operation

theorem same_issued_certificate_different_current_validity :
    issuedObservationView .issuance =
        issuedObservationView .otherPrefix ∧
      currentObservationValidity .issuance ≠
        currentObservationValidity .otherPrefix := by
  constructor
  · rfl
  · intro validityEqual
    have validAtIssuance : currentObservationValidity .issuance := rfl
    have staleAtOtherPrefix :
        ¬ currentObservationValidity .otherPrefix := by
      intro equality
      have observedEqual :=
        congrArg ApparentObservationContent.observedPresent equality
      change true = false at observedEqual
      exact Bool.noConfusion observedEqual
    exact staleAtOtherPrefix (Eq.mp validityEqual validAtIssuance)

end ContextFixture

open ContextFixture

theorem issued_observation_record_does_not_factor_later_validity :
    ¬ ExplicitlyFactorsThrough issuedObservationView
      currentObservationValidity :=
  target_collision_blocks_explicit_factorization
    same_issued_certificate_different_current_validity.1
    same_issued_certificate_different_current_validity.2

theorem issued_observation_derivative_does_not_restore_later_validity
    {Carrier : Type}
    (carrier : ObservationUseContext → Carrier)
    (derived : DerivedOnlyFrom issuedObservationView carrier) :
    ¬ ExplicitlyFactorsThrough carrier currentObservationValidity :=
  derived_view_cannot_restore_target
    issued_observation_record_does_not_factor_later_validity derived

#print axioms issued_observation_record_does_not_factor_later_validity
#print axioms issued_observation_derivative_does_not_restore_later_validity

end LeanProofs.GovernedTransitionBoundariesEvidence
