/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE
  Private-Source-Repository: unpingable/skunkworks
  Private-Source-Commit: b3d73a7a8f3c47486a29767b8b28c809af0f4e57
  Extracted-Tree: 84f209f57e2495463833137cd58aac7ce73e6f96
  Private-Extracted-Source: formalization/PromotionCandidates/V16GovernedTransitionBoundaries/Extracted/LeanProofs/GovernedTransitionBoundariesEvidence/JurisdictionBoundary.lean
  Public-Destination: LeanProofs/GovernedTransitionBoundariesEvidence/JurisdictionBoundary.lean
  Crossing-Campaign-Date: 2026-07-26
  Theorem-Surface: FIXED-POLICY-AUTHORIZATION-REFUSAL-WITNESS
-/

/-
  One fixed native-style policy specimen separating information computation
  from inspection and reliance jurisdiction.
-/

import LeanProofs.GovernedTransitionBoundaries

namespace LeanProofs.GovernedTransitionBoundariesEvidence

open LeanProofs.GovernedTransitionBoundaries

namespace JurisdictionFixture

inductive RepairView where
  | claimOnly
  | fullRepairEvidence
  deriving DecidableEq, Repr

inductive RepairJudgment where
  | effectPresent
  deriving DecidableEq, Repr

structure ConsumerId where
  value : Nat
  deriving DecidableEq, Repr

structure InspectGrant where
  consumer : ConsumerId
  view : RepairView
  deriving DecidableEq, Repr

structure RelianceGrant where
  consumer : ConsumerId
  view : RepairView
  judgment : RepairJudgment
  deriving DecidableEq, Repr

structure ConsumerPolicy where
  inspect : List InspectGrant
  rely : List RelianceGrant
  deriving DecidableEq, Repr

inductive RepairViewValue where
  | claim (effectPresent : Bool)
  | full (effectPresent receiptPresent : Bool)
  deriving DecidableEq, Repr

structure RepairSource where
  effectPresent : Bool
  receiptPresent : Bool
  deriving DecidableEq, Repr

def claimOnlyProjection (source : RepairSource) : RepairViewValue :=
  .claim source.effectPresent

def fullEvidenceProjection (source : RepairSource) : RepairViewValue :=
  .full source.effectPresent source.receiptPresent

def selectedInformationProduct (source : RepairSource) :
    RepairViewValue × RepairViewValue :=
  (claimOnlyProjection source, fullEvidenceProjection source)

def establishedEffectPresent (source : RepairSource) : Bool :=
  source.effectPresent

def effectFromViewValue : RepairViewValue → Bool
  | .claim effect => effect
  | .full effect _ => effect

def AuthorizedToInspect
    (policy : ConsumerPolicy) (consumer : ConsumerId)
    (view : RepairView) : Bool :=
  decide ({ consumer, view } ∈ policy.inspect)

def AuthorizedToRely
    (policy : ConsumerPolicy) (consumer : ConsumerId)
    (judgment : RepairJudgment) (view : RepairView) : Bool :=
  decide ({ consumer, view, judgment } ∈ policy.rely)

def ProductInspectionAuthorized
    (policy : ConsumerPolicy) (consumer : ConsumerId)
    (left right : RepairView) : Bool :=
  AuthorizedToInspect policy consumer left &&
    AuthorizedToInspect policy consumer right

def ProductRelianceAuthorized
    (policy : ConsumerPolicy) (consumer : ConsumerId)
    (judgment : RepairJudgment)
    (left right : RepairView) : Bool :=
  AuthorizedToRely policy consumer judgment left &&
    AuthorizedToRely policy consumer judgment right

def stateConsumer : ConsumerId := { value := 12000 }

/-- Exact projection of the fixed native policy relevant to this specimen. -/
def consumerPolicy : ConsumerPolicy :=
  { inspect :=
      [{ consumer := stateConsumer, view := .claimOnly }]
    rely :=
      [{ consumer := stateConsumer, view := .claimOnly,
         judgment := .effectPresent }] }

theorem selected_product_computes_established_effect :
    ExplicitlyFactorsThrough selectedInformationProduct
      establishedEffectPresent :=
  ⟨fun value => effectFromViewValue value.1, fun _ => rfl⟩

end JurisdictionFixture

open JurisdictionFixture

theorem computationally_sufficient_product_can_be_refused :
    ExplicitlyFactorsThrough selectedInformationProduct
        establishedEffectPresent ∧
      ProductInspectionAuthorized consumerPolicy stateConsumer
        .claimOnly .fullRepairEvidence = false ∧
      ProductRelianceAuthorized consumerPolicy stateConsumer .effectPresent
        .claimOnly .fullRepairEvidence = false :=
  ⟨selected_product_computes_established_effect, rfl, rfl⟩

#print axioms computationally_sufficient_product_can_be_refused

end LeanProofs.GovernedTransitionBoundariesEvidence
