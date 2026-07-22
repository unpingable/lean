/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE
-/

import PJ
import PJ.HeldOut.StaticRole

/-!
  Direct Tranche-A axiom receipts. This leaf is deliberately outside every
  default aggregate and does not ratify the provisional common signature.
-/

#print axioms PJ.IndexedJudgmentBridge.EntitledFrom.targetEvidence
#print axioms PJ.IndexedJudgmentBridge.NotEntitledFrom

#print axioms PJ.Hostile.ExactReceipt.bridge
#print axioms PJ.Hostile.ExactReceipt.bare_target_truth_does_not_supply_receipt
#print axioms PJ.Hostile.ExactReceipt.wrong_source_cannot_replay_receipt
#print axioms PJ.Hostile.ExactReceipt.exact_entitlement
#print axioms PJ.Hostile.ExactReceipt.exact_entitlement_yields_target

#print axioms PJ.Instances.GovernedTransport.positiveTranslationBridge
#print axioms PJ.Instances.GovernedTransport.positiveRelianceBridge
#print axioms PJ.Instances.GovernedTransport.negativeTranslationBridge
#print axioms PJ.Instances.GovernedTransport.negativeRelianceBridge
#print axioms PJ.Instances.GovernedTransport.positiveEntitlementOfCertificateLift
#print axioms PJ.Instances.GovernedTransport.positiveLocalEntitlementOfTranslated
#print axioms PJ.Instances.GovernedTransport.negativeLocalEntitlementOfTranslated
#print axioms PJ.Instances.GovernedTransport.MissingPositiveLiftAdapter.translate
#print axioms PJ.Instances.GovernedTransport.MissingPositiveLiftAdapter.pjBridge
#print axioms PJ.Instances.GovernedTransport.MissingPositiveLiftAdapter.native_missing_lift_remains_not_entitled
#print axioms PJ.Instances.GovernedTransport.TargetLocalNegativeAdapter.translate
#print axioms PJ.Instances.GovernedTransport.TargetLocalNegativeAdapter.pjBridge
#print axioms PJ.Instances.GovernedTransport.TargetLocalNegativeAdapter.target_local_evidence_remains_not_entitled

#print axioms PJ.Instances.ExecutionCustody.ticketFreshToMayAttempt
#print axioms PJ.Instances.ExecutionCustody.mayAttemptToMayCommit
#print axioms PJ.Instances.ExecutionCustody.mayCommitToCommitAttempted
#print axioms PJ.Instances.ExecutionCustody.commitAttemptedToDidExecute
#print axioms PJ.Instances.ExecutionCustody.commitAttemptedToDidNotExecute
#print axioms PJ.Instances.ExecutionCustody.commitAttemptedToCommitUnknown
#print axioms PJ.Instances.ExecutionCustody.didExecuteToPreservedSafety
#print axioms PJ.Instances.ExecutionCustody.obligationReceiptToDischargedObligation
#print axioms PJ.Instances.ExecutionCustody.freshTicketEntitlement
#print axioms PJ.Instances.ExecutionCustody.checkedAttemptEntitlement
#print axioms PJ.Instances.ExecutionCustody.commitAttemptEntitlement
#print axioms PJ.Instances.ExecutionCustody.successfulExecutionEntitlement
#print axioms PJ.Instances.ExecutionCustody.refusedOutcomeEntitlement
#print axioms PJ.Instances.ExecutionCustody.unknownOutcomeEntitlement
#print axioms PJ.Instances.ExecutionCustody.safetyEntitlement
#print axioms PJ.Instances.ExecutionCustody.dischargeEntitlement
#print axioms PJ.Instances.ExecutionCustody.may_attempt_not_entitled_to_commit_without_local_preconditions
#print axioms PJ.Instances.ExecutionCustody.may_commit_not_entitled_to_attempt_without_send
#print axioms PJ.Instances.ExecutionCustody.refused_attempt_entitled_to_refusal_not_execution
#print axioms PJ.Instances.ExecutionCustody.unknown_attempt_entitled_to_neither_outcome
#print axioms PJ.Instances.ExecutionCustody.execution_not_entitled_to_safety_without_witness
#print axioms PJ.Instances.ExecutionCustody.safety_does_not_supply_discharge_receipt

#print axioms PJ.Instances.ContinuityAdmission.wellFormedBridge
#print axioms PJ.Instances.ContinuityAdmission.coherentBridge
#print axioms PJ.Instances.ContinuityAdmission.ownsPacketBridge
#print axioms PJ.Instances.ContinuityAdmission.receipt_identity
#print axioms PJ.Instances.ContinuityAdmission.receipt_compose
#print axioms PJ.Instances.ContinuityAdmission.receipt_preserves_agent_id
#print axioms PJ.Instances.ContinuityAdmission.ownPacketWellFormedEntitlement
#print axioms PJ.Instances.ContinuityAdmission.ownPacketCoherentEntitlement
#print axioms PJ.Instances.ContinuityAdmission.ownPacketOwnershipEntitlement
#print axioms PJ.Instances.ContinuityAdmission.own_packet_entitlements_yield_native_judgments
#print axioms PJ.Instances.ContinuityAdmission.foreign_packet_not_wellformed_entitled
#print axioms PJ.Instances.ContinuityAdmission.foreign_packet_not_coherent_entitled
#print axioms PJ.Instances.ContinuityAdmission.foreign_packet_not_ownership_entitled

#print axioms PJ.HeldOut.StaticRole.r1ToR0ProjectionBridge
#print axioms PJ.HeldOut.StaticRole.r2ToR1ProjectionBridge
#print axioms PJ.HeldOut.StaticRole.r3ToR2ProjectionBridge
#print axioms PJ.HeldOut.StaticRole.r0ToR1Bridge
#print axioms PJ.HeldOut.StaticRole.r1ToR2Bridge
#print axioms PJ.HeldOut.StaticRole.r2ToR3Bridge
#print axioms PJ.HeldOut.StaticRole.exact_entitlements_recover_r1_r2_r3
#print axioms PJ.HeldOut.StaticRole.r0_without_r1_remains_not_entitled
#print axioms PJ.HeldOut.StaticRole.r1_without_r2_remains_not_entitled
#print axioms PJ.HeldOut.StaticRole.r2_without_r3_remains_not_entitled
#print axioms PJ.HeldOut.StaticRole.lawful_reference_transport_boundary
#print axioms PJ.HeldOut.StaticRole.same_reduct_presentation_boundary
#print axioms PJ.HeldOut.StaticRole.factorization_boundary
#print axioms PJ.HeldOut.StaticRole.correctness_boundary
#print axioms PJ.HeldOut.StaticRole.availability_and_consumption_boundaries
