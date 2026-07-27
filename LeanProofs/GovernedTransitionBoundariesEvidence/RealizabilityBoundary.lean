/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE
  Private-Source-Repository: unpingable/skunkworks
  Private-Source-Commit: b3d73a7a8f3c47486a29767b8b28c809af0f4e57
  Extracted-Tree: 84f209f57e2495463833137cd58aac7ce73e6f96
  Private-Extracted-Source: formalization/PromotionCandidates/V16GovernedTransitionBoundaries/Extracted/LeanProofs/GovernedTransitionBoundariesEvidence/RealizabilityBoundary.lean
  Public-Destination: LeanProofs/GovernedTransitionBoundariesEvidence/RealizabilityBoundary.lean
  Crossing-Campaign-Date: 2026-07-26
  Theorem-Surface: BOUNDED-CAPACITY-REALIZABILITY-WITNESS
-/

/-
  Budget-two, unit-demand resource domain with current certificates for every
  selected pair and no selected ordered three-event execution.
-/

import LeanProofs.GovernedTransitionBoundaries

namespace LeanProofs.GovernedTransitionBoundariesEvidence

namespace RealizabilityFixture

inductive ResourceEvent where
  | left
  | right
  | third
  deriving DecidableEq, Repr

structure ResourcePrefix where
  consumed : Nat
  deriving DecidableEq, Repr

def emptyPrefix : ResourcePrefix := { consumed := 0 }
def resourceBudget : Nat := 2
def eventDemand (_ : ResourceEvent) : Nat := 1

structure PairConcurrencyClaim where
  left : ResourceEvent
  right : ResourceEvent
  deriving DecidableEq, Repr

def PairSupportedAt
    (atPrefix : ResourcePrefix) (claim : PairConcurrencyClaim) : Prop :=
  atPrefix.consumed + eventDemand claim.left + eventDemand claim.right ≤
    resourceBudget

structure StateIndexedPairCertificate where
  claim : PairConcurrencyClaim
  establishedAt : ResourcePrefix
  established : PairSupportedAt establishedAt claim

def leftRightCertificate : StateIndexedPairCertificate :=
  { claim := { left := .left, right := .right }
    establishedAt := emptyPrefix
    established := by change 2 ≤ 2; exact Nat.le_refl 2 }

def leftThirdCertificate : StateIndexedPairCertificate :=
  { claim := { left := .left, right := .third }
    establishedAt := emptyPrefix
    established := by change 2 ≤ 2; exact Nat.le_refl 2 }

def rightThirdCertificate : StateIndexedPairCertificate :=
  { claim := { left := .right, right := .third }
    establishedAt := emptyPrefix
    established := by change 2 ≤ 2; exact Nat.le_refl 2 }

structure ExactPairCertificateBundle where
  leftRight : StateIndexedPairCertificate
  leftThird : StateIndexedPairCertificate
  rightThird : StateIndexedPairCertificate

def exactPairCertificates : ExactPairCertificateBundle :=
  { leftRight := leftRightCertificate
    leftThird := leftThirdCertificate
    rightThird := rightThirdCertificate }

def revalidatePair
    (current : ResourcePrefix) (claim : PairConcurrencyClaim) : Prop :=
  PairSupportedAt current claim

def AllExactPairCertificatesCurrent : Prop :=
  revalidatePair emptyPrefix exactPairCertificates.leftRight.claim ∧
    revalidatePair emptyPrefix exactPairCertificates.leftThird.claim ∧
    revalidatePair emptyPrefix exactPairCertificates.rightThird.claim

/-- The fields encode the selected order `left`, `right`, `third`. -/
structure ThreeEventExecution where
  leftEnabledAtEmpty :
    eventDemand .left ≤ resourceBudget
  rightEnabledAfterLeft :
    eventDemand .left + eventDemand .right ≤ resourceBudget
  thirdEnabledAfterLeftRight :
    eventDemand .left + eventDemand .right + eventDemand .third ≤
      resourceBudget

theorem every_exact_pair_certificate_revalidates_at_common_source :
    AllExactPairCertificatesCurrent :=
  ⟨exactPairCertificates.leftRight.established,
    exactPairCertificates.leftThird.established,
    exactPairCertificates.rightThird.established⟩

theorem selected_three_event_execution_domain_is_empty :
    ¬ Nonempty ThreeEventExecution := by
  rintro ⟨execution⟩
  have impossible := execution.thirdEnabledAfterLeftRight
  change 3 ≤ 2 at impossible
  exact Nat.not_succ_le_self 2 impossible

end RealizabilityFixture

open RealizabilityFixture

theorem exact_current_pair_certificates_do_not_instantiate_selected_triple :
    Nonempty ExactPairCertificateBundle ∧
      AllExactPairCertificatesCurrent ∧
      ¬ Nonempty ThreeEventExecution :=
  ⟨⟨exactPairCertificates⟩,
    every_exact_pair_certificate_revalidates_at_common_source,
    selected_three_event_execution_domain_is_empty⟩

#print axioms exact_current_pair_certificates_do_not_instantiate_selected_triple

end LeanProofs.GovernedTransitionBoundariesEvidence
