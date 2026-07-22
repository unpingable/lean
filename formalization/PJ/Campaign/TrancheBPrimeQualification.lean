/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE
-/

import PJ.TrancheBPrime.AntiMinting
import PJ.TrancheBPrime.Instances
import PJ.TrancheBPrime.HeldOutStaticRole

/-!
  Direct axiom receipts for the provisional PJ Tranche B-prime candidate.
  The leaf imports the exact Tranche B-prime source modules directly, so a
  stale aggregate object cannot hide or substitute declarations.  It does not
  ratify the result.
-/

#print axioms PJ.TrancheBPrime.AdmissibleConsumer.consumeEntitled
#print axioms PJ.TrancheBPrime.exact_receipt_prevents_target_minting
#print axioms PJ.TrancheBPrime.EntitlementProjection.present_injective

#print axioms PJ.TrancheBPrime.Hostile.wrong_context_remains_not_entitled
#print axioms PJ.TrancheBPrime.Hostile.wrong_subject_remains_not_entitled
#print axioms PJ.TrancheBPrime.Hostile.no_uniform_receipt_free_minter
#print axioms PJ.TrancheBPrime.Hostile.exact_receipt_is_sufficient_for_bounded_consumer
#print axioms PJ.TrancheBPrime.Hostile.distinct_native_bridges_have_distinct_force
#print axioms PJ.TrancheBPrime.Hostile.wrong_native_bridge_remains_not_interchangeable
#print axioms PJ.TrancheBPrime.Hostile.collapsed_bridge_admits_receipt_free_mint
#print axioms PJ.TrancheBPrime.Hostile.native_receipt_erasure_has_no_left_inverse

#print axioms PJ.TrancheBPrime.Instances.GovernedTransport.true_target_has_no_exact_route
#print axioms PJ.TrancheBPrime.Instances.GovernedTransport.exact_gt_route_gap_is_nonvacuous
#print axioms PJ.TrancheBPrime.Instances.GovernedTransport.exact_gt_receipt_recovers_target
#print axioms PJ.TrancheBPrime.Instances.GovernedTransport.gt_route_bridge_refutes_receipt_free_mint
#print axioms PJ.TrancheBPrime.Instances.GovernedTransport.exact_gt_receipt_permits_bounded_consumption

#print axioms PJ.TrancheBPrime.Instances.ExecutionCustody.different_stage_commit_receipt_is_unavailable
#print axioms PJ.TrancheBPrime.Instances.ExecutionCustody.permission_does_not_mint_committed_attempt
#print axioms PJ.TrancheBPrime.Instances.ExecutionCustody.same_stage_permission_without_send_remains_not_entitled
#print axioms PJ.TrancheBPrime.Instances.ExecutionCustody.exact_execution_receipt_recovers_attempt
#print axioms PJ.TrancheBPrime.Instances.ExecutionCustody.unknown_execution_outcomes_remain_distinct
#print axioms PJ.TrancheBPrime.Instances.ExecutionCustody.execution_bridge_refutes_receipt_free_mint
#print axioms PJ.TrancheBPrime.Instances.ExecutionCustody.exact_execution_receipt_permits_bounded_consumption

#print axioms PJ.TrancheBPrime.Instances.SomeoneContinuity.cross_agent_receipt_is_unavailable
#print axioms PJ.TrancheBPrime.Instances.SomeoneContinuity.packet_truth_does_not_mint_cross_agent_continuity
#print axioms PJ.TrancheBPrime.Instances.SomeoneContinuity.exact_continuity_receipt_recovers_ownership
#print axioms PJ.TrancheBPrime.Instances.SomeoneContinuity.continuity_bridge_refutes_receipt_free_mint
#print axioms PJ.TrancheBPrime.Instances.SomeoneContinuity.exact_continuity_receipt_permits_bounded_consumption

#print axioms PJ.TrancheBPrime.HeldOutStaticRole.faithfulR3Consumer
#print axioms PJ.TrancheBPrime.HeldOutStaticRole.exact_static_role_receipt_is_sufficient
#print axioms PJ.TrancheBPrime.HeldOutStaticRole.r2_truth_does_not_mint_r3_entitlement
#print axioms PJ.TrancheBPrime.HeldOutStaticRole.functional_dependence_remains_local
