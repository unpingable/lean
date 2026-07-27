/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE
  Private-Source-Repository: unpingable/skunkworks
  Private-Source-Commit: b3d73a7a8f3c47486a29767b8b28c809af0f4e57
  Extracted-Tree: 84f209f57e2495463833137cd58aac7ce73e6f96
  Private-Extracted-Source: formalization/PromotionCandidates/V16GovernedTransitionBoundaries/Extracted/LeanProofs/GovernedTransitionBoundariesEvidence/GroundingBoundary.lean
  Public-Destination: LeanProofs/GovernedTransitionBoundariesEvidence/GroundingBoundary.lean
  Crossing-Campaign-Date: 2026-07-26
  Theorem-Surface: MODELED-HIDDEN-RELATION-NONIDENTIFIABILITY-WITNESS
-/

/-
  Two acquisition worlds agreeing on one admitted internal interface and
  differing on one modeled operational relation.
-/

import LeanProofs.GovernedTransitionBoundaries

namespace LeanProofs.GovernedTransitionBoundariesEvidence

open LeanProofs.GovernedTransitionBoundaries

namespace GroundingFixture

structure AcquisitionPolicy where
  declaredDependency : Bool
  deriving DecidableEq, Repr

structure AcquisitionEnvelope where
  acquisition : Nat
  channel : Nat
  producer : Nat
  upstream : Nat
  process : Nat
  authenticator : Nat
  deriving DecidableEq, Repr

inductive CorroborationResult where
  | admitted
  deriving DecidableEq, Repr

inductive OperationalRelation where
  | independent
  | hiddenCommonDependency
  deriving DecidableEq, Repr

structure AcquisitionWorld where
  policy : AcquisitionPolicy
  left : AcquisitionEnvelope
  right : AcquisitionEnvelope
  operational : OperationalRelation
  deriving DecidableEq, Repr

structure DeclaredAcquisitionInterface where
  policy : AcquisitionPolicy
  left : AcquisitionEnvelope
  right : AcquisitionEnvelope
  result : CorroborationResult
  deriving DecidableEq, Repr

def positivePolicy : AcquisitionPolicy :=
  { declaredDependency := false }

def stateEnvelope : AcquisitionEnvelope :=
  { acquisition := 10500, channel := 10000, producer := 10100
    upstream := 10200, process := 10300, authenticator := 10400 }

def markerEnvelope : AcquisitionEnvelope :=
  { acquisition := 10501, channel := 10001, producer := 10101
    upstream := 10201, process := 10301, authenticator := 10401 }

def declaredAcquisitionInterface
    (world : AcquisitionWorld) : DeclaredAcquisitionInterface :=
  { policy := world.policy
    left := world.left
    right := world.right
    result := .admitted }

def operationallyIndependent (world : AcquisitionWorld) : Bool :=
  match world.operational with
  | .independent => true
  | .hiddenCommonDependency => false

def declaredIndependentWorld : AcquisitionWorld :=
  { policy := positivePolicy
    left := stateEnvelope
    right := markerEnvelope
    operational := .independent }

def undeclaredCommonDependencyWorld : AcquisitionWorld :=
  { policy := positivePolicy
    left := stateEnvelope
    right := markerEnvelope
    operational := .hiddenCommonDependency }

theorem declared_interfaces_equal_operational_relations_differ :
    declaredAcquisitionInterface declaredIndependentWorld =
        declaredAcquisitionInterface undeclaredCommonDependencyWorld ∧
      operationallyIndependent declaredIndependentWorld ≠
        operationallyIndependent undeclaredCommonDependencyWorld :=
  ⟨rfl, by intro h; exact Bool.noConfusion h⟩

end GroundingFixture

open GroundingFixture

theorem admitted_acquisition_interface_does_not_factor_modeled_relation :
    ¬ ExplicitlyFactorsThrough declaredAcquisitionInterface
      operationallyIndependent :=
  target_collision_blocks_explicit_factorization
    declared_interfaces_equal_operational_relations_differ.1
    declared_interfaces_equal_operational_relations_differ.2

theorem admitted_interface_derivative_does_not_restore_modeled_relation
    {Carrier : Type}
    (carrier : AcquisitionWorld → Carrier)
    (derived : DerivedOnlyFrom declaredAcquisitionInterface carrier) :
    ¬ ExplicitlyFactorsThrough carrier operationallyIndependent :=
  derived_view_cannot_restore_target
    admitted_acquisition_interface_does_not_factor_modeled_relation derived

#print axioms admitted_acquisition_interface_does_not_factor_modeled_relation
#print axioms admitted_interface_derivative_does_not_restore_modeled_relation

end LeanProofs.GovernedTransitionBoundariesEvidence
