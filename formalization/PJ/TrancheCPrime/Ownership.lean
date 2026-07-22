/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE
-/

import PJ.TrancheBPrime.Instances
import PJ.TrancheBPrime.HeldOutStaticRole
import Continuity.Admission.Qualification.Hostile

/-!
  PJ Tranche C-prime ownership census and hostile boundary.

  Candidate classification: `NO-USEFUL-OWNERSHIP-COMMONALITY`.

  The frozen forcing surfaces expose exact bridge schemas, receipts, and
  local state facts, but none exposes a stateful institution entitled to
  realize a PJ bridge:

  * Governed Transport supplies pure route/translation/reliance evidence;
  * Execution Custody records one complete asserted stage and explicitly
    abstracts the actuator and trajectory-level ticket law;
  * Someone supplies an event-indexed relation and propositional reachability,
    but its events name no realizing institution and its qualified surface
    establishes no durable revocation owner;
  * StaticRole supplies lawful reference actions and presentations without an
    institutional state owner.

  Consequently this module does not add an `Owner` carrier or an institutional
  extension.  It records constructive limits of the ratified PJ core and exact
  native hostile facts which a later owner theory would have to strengthen.
  It adds no generic frontier, residual carrier, composition law, authority,
  execution semantics, or operational correspondence.
-/

namespace PJ.TrancheCPrime.Ownership

open PJ.IndexedJudgmentBridge

universe uSource uTarget uSourceJudgment uTargetJudgment uReceipt uOutput

/-! ## Generic negative boundary: PJ receipts are unrestricted evidence

  Lean evidence can be retained and cited more than once.  The frozen PJ-A
  core therefore does not, by itself, make receipt consumption linear or
  mutate institutional state when a consumer is invoked.  (A local bridge can
  still index a pre/post relation.)  This duplication is not a claim that an
  operational effect happened twice.
-/

/-- An exact PJ entitlement is ordinary reusable evidence.  No state change,
    spend, revocation, or ownership transition is induced by copying it. -/
def duplicateEntitlement
    {bridge : PJ.IndexedJudgmentBridge.{uSource, uTarget,
      uSourceJudgment, uTargetJudgment, uReceipt}}
    {source : bridge.SourceIndex} {target : bridge.TargetIndex}
    (entitlement : bridge.EntitledFrom source target) :
    bridge.EntitledFrom source target ×'
      bridge.EntitledFrom source target :=
  ⟨entitlement, entitlement⟩

/-- Even B-prime's receipt-gated consumer is a pure function and can be
    applied twice to the same proof.  The generic layer prevents target
    minting; it does not own a stateful crossing. -/
def consumeSameEntitlementTwice
    {bridge : PJ.IndexedJudgmentBridge.{uSource, uTarget,
      uSourceJudgment, uTargetJudgment, uReceipt}}
    {source : bridge.SourceIndex} {target : bridge.TargetIndex}
    (consumer : PJ.TrancheBPrime.AdmissibleConsumer.{uOutput}
      bridge source target)
    (entitlement : bridge.EntitledFrom source target) :
    consumer.Output × consumer.Output :=
  ⟨consumer.consumeEntitled entitlement,
    consumer.consumeEntitled entitlement⟩

/-! ## Governed Transport: qualified bridge, no stateful owner -/

namespace GovernedTransport

open PJ.TrancheBPrime.Instances.GovernedTransport

/-- The exact GT receipt can be retained twice because it is route evidence,
    not a linear realization capability. -/
def repeatedExactRouteEvidence :
    incompleteRouteBridge.EntitledFrom () false ×'
      incompleteRouteBridge.EntitledFrom () false :=
  duplicateEntitlement exactFalseEntitlement

/-- A bridge value, source evidence, and inhabited target family still do not
    provide the absent native route.  No missing owner is inferred: the exact
    obstruction is the route receipt already identified by B-prime. -/
theorem bridge_description_does_not_realize_missing_route :
    Nonempty (incompleteRouteBridge.SourceJudgment ()) ∧
      Nonempty (incompleteRouteBridge.TargetJudgment true) ∧
      incompleteRouteBridge.NotEntitledFrom () true :=
  ⟨exact_gt_route_gap_is_nonvacuous.1,
    exact_gt_route_gap_is_nonvacuous.2.1,
    exact_gt_route_gap_is_nonvacuous.2.2.2⟩

end GovernedTransport

/-! ## Execution Custody: state fields without an actuator owner -/

namespace ExecutionCustody

open LeanProofs.BoundedCalculi.ExecutionCustody
open PJ.Instances.ExecutionCustody
open PJ.TrancheBPrime.Instances.ExecutionCustody

/-- The exact attempt entitlement is reusable exact evidence, not a modeled
    historical receipt.  Reuse does not send a second commit and cannot
    establish trajectory-level linearity. -/
def repeatedAttemptEvidence :
    mayCommitToCommitAttempted.EntitledFrom
        successfulCommitStage successfulCommitStage ×'
      mayCommitToCommitAttempted.EntitledFrom
        successfulCommitStage successfulCommitStage :=
  duplicateEntitlement commitAttemptEntitlement

/-- The native stage records ticket consumption and a refused outcome while
    still refuting execution.  These are local state facts, not evidence for a
    generic owner or actuator. -/
theorem spent_stage_does_not_supply_execution :
    TicketSpent refusedCommitStage ∧
      DidNotExecute refusedCommitStage ∧
      ¬ DidExecute refusedCommitStage :=
  ⟨refused_attempt_entitled_to_refusal_not_execution.1,
    refused_attempt_entitled_to_refusal_not_execution.2.1,
    refused_attempt_entitled_to_refusal_not_execution.2.2.1⟩

/-- The bridge schema exists at a stage where its exact send/consumption
    receipt does not.  Thus the bridge description is not a stateful mechanism
    which realizes itself. -/
theorem bridge_schema_does_not_realize_attempt :
    MayCommit commitNotAttemptedStage ∧
      ¬ CommitAttempted commitNotAttemptedStage ∧
      mayCommitToCommitAttempted.NotEntitledFrom
        commitNotAttemptedStage commitNotAttemptedStage :=
  ⟨same_stage_permission_without_send_remains_not_entitled.1,
    same_stage_permission_without_send_remains_not_entitled.2.1,
    same_stage_permission_without_send_remains_not_entitled.2.2.2⟩

end ExecutionCustody

/-! ## Someone Continuity: local transition theory without durable owner -/

namespace ContinuityAdmission

open Continuity.Admission
open PJ.Instances.ContinuityAdmission
open PJ.TrancheBPrime.Instances.ContinuityAdmission

/-- Native reachability is a reusable proposition.  Reusing its PJ
    entitlement does not enact the admission path a second time. -/
def repeatedReachabilityEvidence :
    ownsPacketBridge.EntitledFrom
        (initial johnId)
        ⟨johnId, targetState (acceptedPacket johnAdmission),
          some (acceptedPacket johnAdmission)⟩ ×'
      ownsPacketBridge.EntitledFrom
        (initial johnId)
        ⟨johnId, targetState (acceptedPacket johnAdmission),
          some (acceptedPacket johnAdmission)⟩ :=
  duplicateEntitlement
    (ownPacketOwnershipEntitlement johnId johnAdmission rfl)

/-- Exact native hostile: an authority breach drops the packet, after which
    the unchanged packet can be resubmitted and accepted.  The ratified source
    therefore does not provide the durable revocation/reconstruction law that
    a stateful continuity owner would require. -/
theorem breach_reuses_exact_packet_after_demotion :
    step john (.fault .authorityBreach) (initial johnId) ∧
    step (initial johnId) .startForging
      (Continuity.Admission.Qualification.Hostile.forgingAgent johnId) ∧
    step (Continuity.Admission.Qualification.Hostile.forgingAgent johnId)
      .submitAdmission
      (Continuity.Admission.Qualification.Hostile.candidateAgent
        johnId johnAdmission) ∧
    step (Continuity.Admission.Qualification.Hostile.candidateAgent
      johnId johnAdmission)
      .humanAccept john :=
  Continuity.Admission.Qualification.Hostile.breach_sequence_reuses_exact_packet

/-- Local ownership truths at both endpoints do not manufacture a
    cross-agent realization receipt.  Packet ownership is an indexed
    invariant, not an institution entitled to perform arbitrary crossings. -/
theorem local_packet_ownership_does_not_supply_cross_agent_receipt :
    OwnsPacket (initial johnId) ∧
      OwnsPacket (initial gwenId) ∧
      ownsPacketBridge.NotEntitledFrom
        (initial johnId) (initial gwenId) :=
  packet_truth_does_not_mint_cross_agent_continuity

end ContinuityAdmission

/-! ## StaticRole counterexample to generic institutional ownership -/

namespace StaticRole

open PJ.HeldOut.StaticRole
open _root_.StaticRole
open _root_.StaticRole.Countermodels.CoherenceHostiles
open _root_.StaticRole.Countermodels.UptakeHostiles

/-- The exact R2-to-R3 entitlement is reusable evidence over lawful
    presentation/evaluation structure.  StaticRole has no institutional
    prestate or realizing owner for PJ to generalize. -/
def repeatedFunctionalEvidence :
    (r2ToR3Bridge coherenceFrame parityAction faithfulUptake).EntitledFrom
        (false, true) (false, true) ×'
      (r2ToR3Bridge coherenceFrame parityAction faithfulUptake).EntitledFrom
        (false, true) (false, true) :=
  duplicateEntitlement coherenceR2ToR3Entitlement

/-- A complete R2 judgment plus a bridge schema does not supply R3 through a
    neutralizing presentation.  The missing structure is StaticRole-local
    functional dependence, not a generic stateful owner. -/
theorem lawful_action_does_not_supply_functional_uptake :
    ProspectiveDeSeEncoding coherenceFrame parityAction false true ∧
      IndexedJudgmentBridge.NotEntitledFrom
        (r2ToR3Bridge coherenceFrame parityAction neutralizingUptake)
        (false, true) (false, true) :=
  r2_without_r3_remains_not_entitled

end StaticRole

#print axioms duplicateEntitlement
#print axioms consumeSameEntitlementTwice
#print axioms GovernedTransport.repeatedExactRouteEvidence
#print axioms GovernedTransport.bridge_description_does_not_realize_missing_route
#print axioms ExecutionCustody.repeatedAttemptEvidence
#print axioms ExecutionCustody.spent_stage_does_not_supply_execution
#print axioms ExecutionCustody.bridge_schema_does_not_realize_attempt
#print axioms ContinuityAdmission.repeatedReachabilityEvidence
#print axioms ContinuityAdmission.breach_reuses_exact_packet_after_demotion
#print axioms ContinuityAdmission.local_packet_ownership_does_not_supply_cross_agent_receipt
#print axioms StaticRole.repeatedFunctionalEvidence
#print axioms StaticRole.lawful_action_does_not_supply_functional_uptake

end PJ.TrancheCPrime.Ownership
