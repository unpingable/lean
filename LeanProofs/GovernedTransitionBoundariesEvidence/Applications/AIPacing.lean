/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE
  Private-Source-Repository: unpingable/skunkworks
  Private-Source-Commit: 3b9a673633b7778d140a2f80f1251913eb35717f
  Private-Source-Path: formalization/Skunkworks/TransitionRelativeComputation/AIPacingInstantiation.lean
  Public-Destination: LeanProofs/GovernedTransitionBoundariesEvidence/Applications/AIPacing.lean
  Promotion-Date: 2026-07-28
  Theorem-Surface: AI-PACING-APPLICATION-CASE
-/

/-
  A finite application case for a bounded external model evaluation used in a
  later deployment-certification decision.

  The local access, time, and beneficiary coordinates expose what this case
  needs without adding a general access-governance, cross-artifact transport,
  or public-representation calculus.
-/

import LeanProofs.GovernedTransitionBoundariesEvidence.JurisdictionBoundary

namespace LeanProofs.GovernedTransitionBoundariesEvidence.Applications.AIPacing

open LeanProofs.GovernedTransitionBoundaries
open LeanProofs.GovernedTransitionBoundariesEvidence.JurisdictionFixture

/-! ## Concrete parties, artifacts, and bounded evaluation -/

structure ProviderId where
  value : Nat
  deriving DecidableEq, Repr

structure EvaluatorId where
  value : Nat
  deriving DecidableEq, Repr

structure ArtifactId where
  value : Nat
  deriving DecidableEq, Repr

structure HarnessId where
  value : Nat
  deriving DecidableEq, Repr

structure EvaluationId where
  value : Nat
  deriving DecidableEq, Repr

structure DeploymentId where
  value : Nat
  deriving DecidableEq, Repr

structure BeneficiaryId where
  value : Nat
  deriving DecidableEq, Repr

/-- Case-local harness ownership coordinate. -/
structure Harness where
  id : HarnessId
  controller : EvaluatorId
  deriving DecidableEq, Repr

/-- Case-local provider controls for the two selected access conditions. -/
structure SelectedAccessConditions where
  providerMayWithhold : Bool
  providerMayRevoke : Bool
  providerMayCurate : Bool
  providerMaySchedule : Bool
  deriving DecidableEq, Repr

def providerIndependentAccess (access : SelectedAccessConditions) : Bool :=
  !access.providerMayWithhold &&
    !access.providerMayRevoke &&
    !access.providerMayCurate &&
    !access.providerMaySchedule

structure BoundedFinding where
  evaluator : EvaluatorId
  evaluatedArtifact : ArtifactId
  evaluation : EvaluationId
  supportsBoundedClaim : Bool
  acquiredAt : Nat
  deriving DecidableEq, Repr

structure EvaluationConditions where
  provider : ProviderId
  evaluator : EvaluatorId
  evaluatedArtifact : ArtifactId
  harness : Harness
  access : SelectedAccessConditions
  evaluation : EvaluationId
  residue : BoundedFinding
  deriving DecidableEq, Repr

def methodIndependent (conditions : EvaluationConditions) : Bool :=
  decide (conditions.harness.controller = conditions.evaluator)

def L : ProviderId := { value := 1500 }
def E : EvaluatorId := { value := 1501 }
def M_eval : ArtifactId := { value := 1502 }

/-- The fully admitted expressible fragment uses exact artifact identity. -/
def M_deploy : ArtifactId := M_eval

/-- A distinct deployed artifact is named, but no relation from `M_eval` to
    this artifact is introduced by this case study. -/
def M_deployChanged : ArtifactId := { value := 1503 }

def H : Harness :=
  { id := { value := 1504 }, controller := E }

/-- `A`: granted access under all four selected provider controls. -/
def A : SelectedAccessConditions :=
  { providerMayWithhold := true
    providerMayRevoke := true
    providerMayCurate := true
    providerMaySchedule := true }

/-- Positive access-independence control. "Compelled" is only the case label. -/
def A_compelled : SelectedAccessConditions :=
  { providerMayWithhold := false
    providerMayRevoke := false
    providerMayCurate := false
    providerMaySchedule := false }

def B : EvaluationId := { value := 1505 }

def R : BoundedFinding :=
  { evaluator := E
    evaluatedArtifact := M_eval
    evaluation := B
    supportsBoundedClaim := true
    acquiredAt := 100 }

def grantedRevocableCase : EvaluationConditions :=
  { provider := L
    evaluator := E
    evaluatedArtifact := M_eval
    harness := H
    access := A
    evaluation := B
    residue := R }

def compelledAccessCase : EvaluationConditions :=
  { grantedRevocableCase with access := A_compelled }

def residueProjection (conditions : EvaluationConditions) : BoundedFinding :=
  conditions.residue

theorem method_and_access_controls_are_distinguished :
    methodIndependent grantedRevocableCase = true ∧
      providerIndependentAccess grantedRevocableCase.access = false ∧
      methodIndependent compelledAccessCase = true ∧
      providerIndependentAccess compelledAccessCase.access = true := by
  decide

/-- The same bounded residue is compatible with both selected access regimes.
    This is not a sufficiency claim for either regime. -/
theorem bounded_residue_does_not_establish_access_independence :
    ¬ ExplicitlyFactorsThrough residueProjection
      (fun conditions => providerIndependentAccess conditions.access) := by
  apply target_collision_blocks_explicit_factorization
    (left := grantedRevocableCase) (right := compelledAccessCase)
  · rfl
  · decide

/-! ## Exact target support and the later deployment claim -/

structure DeploymentClaim where
  transition : DeploymentId
  deployedArtifact : ArtifactId
  dependency : Nat
  deriving DecidableEq, Repr

structure SelectedDeploymentContext where
  deployedArtifact : ArtifactId
  dependency : Nat
  evidenceCurrent : Bool
  deriving DecidableEq, Repr

def T : DeploymentId := { value := 1510 }

def C : DeploymentClaim :=
  { transition := T
    deployedArtifact := M_deploy
    dependency := 71 }

def G : ConsumerId := { value := 1511 }
def P : BeneficiaryId := { value := 1512 }
def certificationPurpose : Nat := 1513

def exactTargetSupport
    (context : SelectedDeploymentContext) (claim : DeploymentClaim) : Bool :=
  context.evidenceCurrent &&
    decide (context.deployedArtifact = claim.deployedArtifact) &&
    decide (context.dependency = claim.dependency)

def evaluatedDeploymentContext : SelectedDeploymentContext :=
  { deployedArtifact := M_deploy
    dependency := C.dependency
    evidenceCurrent := true }

def laterDeploymentContext : SelectedDeploymentContext :=
  { evaluatedDeploymentContext with dependency := 72 }

inductive DeploymentWorld where
  | evaluatedConfiguration
  | laterConfiguration
  deriving DecidableEq, Repr

def boundedFinding (_world : DeploymentWorld) : BoundedFinding :=
  R

def targetContext : DeploymentWorld → SelectedDeploymentContext
  | .evaluatedConfiguration => evaluatedDeploymentContext
  | .laterConfiguration => laterDeploymentContext

def deploymentClaimStanding (world : DeploymentWorld) : Bool :=
  exactTargetSupport (targetContext world) C

theorem bounded_finding_collision_at_deployment_target :
    boundedFinding .evaluatedConfiguration =
        boundedFinding .laterConfiguration ∧
      deploymentClaimStanding .evaluatedConfiguration ≠
        deploymentClaimStanding .laterConfiguration := by
  decide

/-- The bounded finding alone does not uniformly determine standing for the
    exact later deployment claim. -/
theorem bounded_finding_does_not_transport_to_deployment_claim :
    ¬ ExplicitlyFactorsThrough boundedFinding deploymentClaimStanding :=
  target_collision_blocks_explicit_factorization
    bounded_finding_collision_at_deployment_target.1
    bounded_finding_collision_at_deployment_target.2

/-! ## Explicit time, reliance, and separate deployment authorization -/

inductive FindingStanding where
  | current
  | futureDated
  deriving DecidableEq, Repr

def assessFindingAt
    (evaluatedAt : Nat) (finding : BoundedFinding) : FindingStanding :=
  if finding.acquiredAt ≤ evaluatedAt then .current else .futureDated

def findingSupportsDeploymentClaim
    (context : SelectedDeploymentContext) (finding : BoundedFinding)
    (evaluatedAt : Nat) (claim : DeploymentClaim) : Bool :=
  finding.supportsBoundedClaim &&
    decide (finding.evaluatedArtifact = claim.deployedArtifact) &&
    decide (assessFindingAt evaluatedAt finding = .current) &&
    exactTargetSupport context claim

def reliancePolicy : ConsumerPolicy :=
  { inspect := []
    rely :=
      [{ consumer := G
         view := .claimOnly
         judgment := .effectPresent },
       { consumer := G
         view := .fullRepairEvidence
         judgment := .effectPresent }] }

def otherConsumer : ConsumerId := { value := 1599 }

def otherConsumerPolicy : ConsumerPolicy :=
  { reliancePolicy with
    rely :=
      [{ consumer := otherConsumer
         view := .claimOnly
         judgment := .effectPresent },
       { consumer := otherConsumer
         view := .fullRepairEvidence
         judgment := .effectPresent }] }

def OperationalMayRely
    (policy : ConsumerPolicy) (context : SelectedDeploymentContext)
    (finding : BoundedFinding) (evaluatedAt : Nat)
    (consumer : ConsumerId) (purpose : Nat)
    (claim : DeploymentClaim) : Bool :=
  findingSupportsDeploymentClaim context finding evaluatedAt claim &&
    ProductRelianceAuthorized policy consumer .effectPresent
      .claimOnly .fullRepairEvidence &&
    decide (purpose = certificationPurpose)

inductive ProposalRefusal where
  | operationalRelianceNotEstablished
  deriving DecidableEq, Repr

inductive CertificationDecision where
  | ok (claim : DeploymentClaim)
  | error (reason : ProposalRefusal)
  deriving DecidableEq, Repr

def prepareCertification
    (policy : ConsumerPolicy) (context : SelectedDeploymentContext)
    (finding : BoundedFinding) (evaluatedAt : Nat)
    (consumer : ConsumerId) (purpose : Nat)
    (claim : DeploymentClaim) : CertificationDecision :=
  if OperationalMayRely policy context finding evaluatedAt
      consumer purpose claim
  then .ok claim
  else .error .operationalRelianceNotEstablished

/-- Exact target support does not override the separately indexed reliance
    policy. -/
theorem valid_target_transport_with_unauthorized_reliance_is_refused :
    findingSupportsDeploymentClaim evaluatedDeploymentContext R 110 C = true ∧
      OperationalMayRely otherConsumerPolicy evaluatedDeploymentContext
          R 110 G certificationPurpose C = false ∧
      prepareCertification otherConsumerPolicy evaluatedDeploymentContext
          R 110 G certificationPurpose C =
        .error .operationalRelianceNotEstablished := by
  decide

structure DeploymentAuthorization where
  claim : DeploymentClaim
  deriving DecidableEq, Repr

def deploymentAuthorization : DeploymentAuthorization :=
  { claim := C }

def AuthorizedBy
    (authorizations : List DeploymentAuthorization)
    (claim : DeploymentClaim) : Bool :=
  decide ({ claim := claim } ∈ authorizations)

/-- Valid support remains inert without the separately supplied deployment
    authorization. -/
theorem supported_claim_does_not_mint_deployment_authorization :
    prepareCertification reliancePolicy evaluatedDeploymentContext
        R 110 G certificationPurpose C = .ok C ∧
      AuthorizedBy [] C = false := by
  decide

def futureR : BoundedFinding :=
  { R with acquiredAt := 200 }

/-- This result uses explicit acquisition and decision times. It is not an
    ordinary consequence of an unindexed factorization edge. -/
theorem future_ex_post_residue_cannot_supply_present_reliance :
    assessFindingAt 110 futureR = .futureDated ∧
      OperationalMayRely reliancePolicy evaluatedDeploymentContext
          futureR 110 G certificationPurpose C = false ∧
      prepareCertification reliancePolicy evaluatedDeploymentContext
          futureR 110 G certificationPurpose C =
        .error .operationalRelianceNotEstablished := by
  decide

/-- Positive control for the expressible fragment: exact artifact identity,
    current bounded support, exact target dependencies, exact consumer and
    purpose, and a separately supplied authorization. -/
theorem fully_admitted_expressible_fragment :
    findingSupportsDeploymentClaim evaluatedDeploymentContext R 110 C = true ∧
      prepareCertification reliancePolicy evaluatedDeploymentContext
          R 110 G certificationPurpose C = .ok C ∧
      AuthorizedBy [deploymentAuthorization] C = true := by
  decide

/-! ## The missing on-behalf-of-public coordinate -/

inductive PublicAuthorityWorld where
  | selectedDelegatedConsenting
  | nonSelectingNonConsenting
  deriving DecidableEq, Repr

def publicSelectedEvaluator : PublicAuthorityWorld → Bool
  | .selectedDelegatedConsenting => true
  | .nonSelectingNonConsenting => false

def publicGrantedReliance : PublicAuthorityWorld → Bool
  | .selectedDelegatedConsenting => true
  | .nonSelectingNonConsenting => false

def publicConsentedToRisk : PublicAuthorityWorld → Bool
  | .selectedDelegatedConsenting => true
  | .nonSelectingNonConsenting => false

def authorizedRelianceForP (world : PublicAuthorityWorld) : Bool :=
  decide (P = P) &&
    publicSelectedEvaluator world &&
    publicGrantedReliance world &&
    publicConsentedToRisk world

def regulatorReliance (_world : PublicAuthorityWorld) : Bool :=
  OperationalMayRely reliancePolicy evaluatedDeploymentContext
    R 110 G certificationPurpose C

theorem regulator_reliance_collision_at_public_authority :
    regulatorReliance .selectedDelegatedConsenting =
        regulatorReliance .nonSelectingNonConsenting ∧
      authorizedRelianceForP .selectedDelegatedConsenting ≠
        authorizedRelianceForP .nonSelectingNonConsenting := by
  decide

/-- The native regulator-consumer result cannot determine the added local
    beneficiary-authority target. -/
theorem regulator_reliance_does_not_establish_public_authority :
    ¬ ExplicitlyFactorsThrough regulatorReliance authorizedRelianceForP :=
  target_collision_blocks_explicit_factorization
    regulator_reliance_collision_at_public_authority.1
    regulator_reliance_collision_at_public_authority.2

#print axioms bounded_finding_does_not_transport_to_deployment_claim
#print axioms valid_target_transport_with_unauthorized_reliance_is_refused
#print axioms future_ex_post_residue_cannot_supply_present_reliance
#print axioms supported_claim_does_not_mint_deployment_authorization
#print axioms regulator_reliance_does_not_establish_public_authority
#print axioms bounded_residue_does_not_establish_access_independence
#print axioms fully_admitted_expressible_fragment

end LeanProofs.GovernedTransitionBoundariesEvidence.Applications.AIPacing
