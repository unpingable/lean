/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE
  Private-Source-Repository: unpingable/skunkworks
  Private-Source-Commit: b3d73a7a8f3c47486a29767b8b28c809af0f4e57
  Extracted-Tree: 84f209f57e2495463833137cd58aac7ce73e6f96
  Private-Extracted-Source: formalization/PromotionCandidates/V16GovernedTransitionBoundaries/Extracted/LeanProofs/GovernedTransitionBoundariesEvidence/HistoricalBoundary.lean
  Public-Destination: LeanProofs/GovernedTransitionBoundariesEvidence/HistoricalBoundary.lean
  Crossing-Campaign-Date: 2026-07-26
  Theorem-Surface: OCCURRENCE-LINK-OBSERVATION-WITNESS
-/

/-
  Two present-evidence worlds with the same selected present-state view and
  different values for one exact occurrence-link Boolean.
-/

import LeanProofs.GovernedTransitionBoundaries

namespace LeanProofs.GovernedTransitionBoundariesEvidence

open LeanProofs.GovernedTransitionBoundaries

namespace HistoricalFixture

structure TargetId where
  value : Nat
  deriving DecidableEq, Repr

structure StateId where
  value : Nat
  deriving DecidableEq, Repr

structure IntendedCondition where
  target : TargetId
  state : StateId
  deriving DecidableEq, Repr

inductive PresentEvidenceWorld where
  | occurrenceLinked
  | matchingOnly
  deriving DecidableEq, Repr

def selectedIntendedCondition : IntendedCondition :=
  { target := { value := 70 }, state := { value := 71 } }

def presentStateView :
    PresentEvidenceWorld → IntendedCondition × Bool
  | .occurrenceLinked => (selectedIntendedCondition, true)
  | .matchingOnly => (selectedIntendedCondition, true)

def exactOccurrenceLinkObserved : PresentEvidenceWorld → Bool
  | .occurrenceLinked => true
  | .matchingOnly => false

theorem same_present_state_different_occurrence_link :
    presentStateView .occurrenceLinked =
        presentStateView .matchingOnly ∧
      exactOccurrenceLinkObserved .occurrenceLinked ≠
        exactOccurrenceLinkObserved .matchingOnly :=
  ⟨rfl, by intro h; exact Bool.noConfusion h⟩

end HistoricalFixture

open HistoricalFixture

theorem present_state_does_not_factor_occurrence_link :
    ¬ ExplicitlyFactorsThrough presentStateView
      exactOccurrenceLinkObserved :=
  target_collision_blocks_explicit_factorization
    same_present_state_different_occurrence_link.1
    same_present_state_different_occurrence_link.2

theorem present_state_derivative_does_not_restore_occurrence_link
    {Carrier : Type}
    (carrier : PresentEvidenceWorld → Carrier)
    (derived : DerivedOnlyFrom presentStateView carrier) :
    ¬ ExplicitlyFactorsThrough carrier exactOccurrenceLinkObserved :=
  derived_view_cannot_restore_target
    present_state_does_not_factor_occurrence_link derived

#print axioms present_state_does_not_factor_occurrence_link
#print axioms present_state_derivative_does_not_restore_occurrence_link

end LeanProofs.GovernedTransitionBoundariesEvidence
