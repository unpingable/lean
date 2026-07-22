/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE
-/

import PJ.Core
import LeanProofs.BoundedCalculi.ExecutionCustody

/-!
  PJ Tranche-A adapter for the exact public Execution Custody calculus.

  Each bridge below is one native constructor edge.  Source and target indices
  are both the complete `ExecutionStage`; every receipt proves that they are
  the very same stage.  Constructor premises not already supplied by the
  source judgment remain explicit in the receipt.

  Refusal and unknown outcomes are deliberately separate bridges and separate
  target judgment families.  This file adds no generic composition, outcome
  sum, actuator semantics, trajectory-level ticket law, or execution claim.
-/

namespace PJ.Instances.ExecutionCustody

open LeanProofs.BoundedCalculi.ExecutionCustody

/-! ## Exact same-stage receipt shapes -/

/-- Evidence that a native Execution Custody rule is being applied without
    changing its complete stage index. -/
structure ExactStageReceipt (source target : ExecutionStage) : Prop where
  sameStage : source = target

/-- Same-stage evidence plus the exact constructor premise not provided by the
    source judgment. -/
structure ExactStageReceiptWith
    (condition : ExecutionStage → Prop)
    (source target : ExecutionStage) : Prop where
  sameStage : source = target
  conditionAtSource : condition source

def AttemptPremises (stage : ExecutionStage) : Prop :=
  TicketConsumed stage ∧ stage.commitSent = true

def SuccessPremise (stage : ExecutionStage) : Prop :=
  stage.outcome = SubstrateOutcome.succeeded

def RefusalPremise (stage : ExecutionStage) : Prop :=
  stage.outcome = SubstrateOutcome.refused

def UnknownPremise (stage : ExecutionStage) : Prop :=
  stage.outcome = SubstrateOutcome.unknown

def SafetyPremise (stage : ExecutionStage) : Prop :=
  stage.safetyWitness = true

/-! ## One bridge for each native constructor edge -/

def ticketFreshToMayAttempt : PJ.IndexedJudgmentBridge where
  SourceIndex := ExecutionStage
  TargetIndex := ExecutionStage
  SourceJudgment := TicketFresh
  TargetJudgment := MayAttempt
  Receipt := ExactStageReceipt
  carry := by
    intro source target receipt hfresh
    cases receipt.sameStage
    exact MayAttempt.freshTicket hfresh

def mayAttemptToMayCommit : PJ.IndexedJudgmentBridge where
  SourceIndex := ExecutionStage
  TargetIndex := ExecutionStage
  SourceJudgment := MayAttempt
  TargetJudgment := MayCommit
  Receipt := ExactStageReceiptWith LocalPreconditions
  carry := by
    intro source target receipt hattempt
    cases receipt.sameStage
    exact MayCommit.checked hattempt receipt.conditionAtSource

def mayCommitToCommitAttempted : PJ.IndexedJudgmentBridge where
  SourceIndex := ExecutionStage
  TargetIndex := ExecutionStage
  SourceJudgment := MayCommit
  TargetJudgment := CommitAttempted
  Receipt := ExactStageReceiptWith AttemptPremises
  carry := by
    intro source target receipt hcommit
    cases receipt.sameStage
    exact CommitAttempted.sent hcommit
      receipt.conditionAtSource.1 receipt.conditionAtSource.2

def commitAttemptedToDidExecute : PJ.IndexedJudgmentBridge where
  SourceIndex := ExecutionStage
  TargetIndex := ExecutionStage
  SourceJudgment := CommitAttempted
  TargetJudgment := DidExecute
  Receipt := ExactStageReceiptWith SuccessPremise
  carry := by
    intro source target receipt hattempt
    cases receipt.sameStage
    exact DidExecute.substrateSuccess hattempt receipt.conditionAtSource

def commitAttemptedToDidNotExecute : PJ.IndexedJudgmentBridge where
  SourceIndex := ExecutionStage
  TargetIndex := ExecutionStage
  SourceJudgment := CommitAttempted
  TargetJudgment := DidNotExecute
  Receipt := ExactStageReceiptWith RefusalPremise
  carry := by
    intro source target receipt hattempt
    cases receipt.sameStage
    exact DidNotExecute.substrateRefused hattempt receipt.conditionAtSource

def commitAttemptedToCommitUnknown : PJ.IndexedJudgmentBridge where
  SourceIndex := ExecutionStage
  TargetIndex := ExecutionStage
  SourceJudgment := CommitAttempted
  TargetJudgment := CommitUnknown
  Receipt := ExactStageReceiptWith UnknownPremise
  carry := by
    intro source target receipt hattempt
    cases receipt.sameStage
    exact CommitUnknown.substrateUnknown hattempt receipt.conditionAtSource

def didExecuteToPreservedSafety : PJ.IndexedJudgmentBridge where
  SourceIndex := ExecutionStage
  TargetIndex := ExecutionStage
  SourceJudgment := DidExecute
  TargetJudgment := PreservedSafety
  Receipt := ExactStageReceiptWith SafetyPremise
  carry := by
    intro source target receipt hexecuted
    cases receipt.sameStage
    exact PreservedSafety.postStateWitness hexecuted receipt.conditionAtSource

/-- The discharge constructor is intentionally not made downstream of safety:
    its exact native source evidence is the obligation-receipt field itself. -/
def obligationReceiptToDischargedObligation : PJ.IndexedJudgmentBridge where
  SourceIndex := ExecutionStage
  TargetIndex := ExecutionStage
  SourceJudgment := fun stage => stage.obligationReceipt = true
  TargetJudgment := DischargedObligation
  Receipt := ExactStageReceipt
  carry := by
    intro source target receipt hobligation
    cases receipt.sameStage
    exact DischargedObligation.receipt hobligation

/-! ## Exact adapter contact -/

def freshTicketEntitlement :
    ticketFreshToMayAttempt.EntitledFrom
      successfulCommitStage successfulCommitStage :=
  ⟨rfl, ⟨rfl⟩⟩

def checkedAttemptEntitlement :
    mayAttemptToMayCommit.EntitledFrom mayCommitStage mayCommitStage :=
  ⟨MayAttempt.freshTicket rfl, ⟨rfl, ⟨rfl, rfl⟩⟩⟩

def commitAttemptEntitlement :
    mayCommitToCommitAttempted.EntitledFrom
      successfulCommitStage successfulCommitStage :=
  ⟨successfulCommitStage_mayCommit, ⟨rfl, ⟨rfl, rfl⟩⟩⟩

def successfulExecutionEntitlement :
    commitAttemptedToDidExecute.EntitledFrom
      successfulCommitStage successfulCommitStage :=
  ⟨successfulCommitStage_attempted, ⟨rfl, rfl⟩⟩

def refusedOutcomeEntitlement :
    commitAttemptedToDidNotExecute.EntitledFrom
      refusedCommitStage refusedCommitStage :=
  ⟨refusedCommitStage_attempted, ⟨rfl, rfl⟩⟩

def unknownOutcomeEntitlement :
    commitAttemptedToCommitUnknown.EntitledFrom
      unknownCommitStage unknownCommitStage :=
  ⟨unknownCommitStage_attempted, ⟨rfl, rfl⟩⟩

def safetyEntitlement :
    didExecuteToPreservedSafety.EntitledFrom safeExecutedStage safeExecutedStage :=
  ⟨safeExecutedStage_didExecute, ⟨rfl, rfl⟩⟩

def dischargeEntitlement :
    obligationReceiptToDischargedObligation.EntitledFrom
      obligationDischargedStage obligationDischargedStage :=
  ⟨rfl, ⟨rfl⟩⟩

/-! ## Local non-collapse retained through the PJ interface -/

theorem may_attempt_not_entitled_to_commit_without_local_preconditions :
    MayAttempt attemptOnlyStage ∧
      ¬ MayCommit attemptOnlyStage ∧
      mayAttemptToMayCommit.NotEntitledFrom attemptOnlyStage attemptOnlyStage := by
  refine ⟨MayAttempt.freshTicket rfl, ?_, ?_⟩
  · intro hcommit
    cases hcommit with
    | checked _ hlocal => cases hlocal.1
  · intro entitled
    have hcommit := entitled.targetEvidence
    cases hcommit with
    | checked _ hlocal => cases hlocal.1

theorem may_commit_not_entitled_to_attempt_without_send :
    MayCommit commitNotAttemptedStage ∧
      ¬ CommitAttempted commitNotAttemptedStage ∧
      ¬ DidExecute commitNotAttemptedStage ∧
      mayCommitToCommitAttempted.NotEntitledFrom
        commitNotAttemptedStage commitNotAttemptedStage := by
  refine ⟨checked_fresh_ticket_local_preconditions_yields_mayCommit
      rfl ⟨rfl, rfl⟩, ?_, ?_, ?_⟩
  · intro hattempt
    cases hattempt with
    | sent _ _ hsent => cases hsent
  · intro hexecuted
    cases hexecuted with
    | substrateSuccess hattempt _ =>
        cases hattempt with
        | sent _ _ hsent => cases hsent
  · intro entitled
    have hattempt := entitled.targetEvidence
    cases hattempt with
    | sent _ _ hsent => cases hsent

theorem refused_attempt_entitled_to_refusal_not_execution :
    TicketSpent refusedCommitStage ∧
      DidNotExecute refusedCommitStage ∧
      ¬ DidExecute refusedCommitStage ∧
      commitAttemptedToDidExecute.NotEntitledFrom
        refusedCommitStage refusedCommitStage ∧
      commitAttemptedToCommitUnknown.NotEntitledFrom
        refusedCommitStage refusedCommitStage := by
  refine ⟨rfl, refusedOutcomeEntitlement.targetEvidence, ?_, ?_, ?_⟩
  · intro hexecuted
    cases hexecuted with
    | substrateSuccess _ hsuccess => cases hsuccess
  · intro entitled
    have hexecuted := entitled.targetEvidence
    cases hexecuted with
    | substrateSuccess _ hsuccess => cases hsuccess
  · intro entitled
    have hunknown := entitled.targetEvidence
    cases hunknown with
    | substrateUnknown _ hresult => cases hresult

theorem unknown_attempt_entitled_to_neither_outcome :
    CommitUnknown unknownCommitStage ∧
      ¬ DidExecute unknownCommitStage ∧
      ¬ DidNotExecute unknownCommitStage ∧
      commitAttemptedToDidExecute.NotEntitledFrom
        unknownCommitStage unknownCommitStage ∧
      commitAttemptedToDidNotExecute.NotEntitledFrom
        unknownCommitStage unknownCommitStage := by
  refine ⟨unknownOutcomeEntitlement.targetEvidence, ?_, ?_, ?_, ?_⟩
  · intro hexecuted
    cases hexecuted with
    | substrateSuccess _ hsuccess => cases hsuccess
  · intro hrefused
    cases hrefused with
    | substrateRefused _ hresult => cases hresult
  · intro entitled
    have hexecuted := entitled.targetEvidence
    cases hexecuted with
    | substrateSuccess _ hsuccess => cases hsuccess
  · intro entitled
    have hrefused := entitled.targetEvidence
    cases hrefused with
    | substrateRefused _ hrefusal => cases hrefusal

theorem execution_not_entitled_to_safety_without_witness :
    DidExecute successfulCommitStage ∧
      ¬ PreservedSafety successfulCommitStage ∧
      didExecuteToPreservedSafety.NotEntitledFrom
        successfulCommitStage successfulCommitStage := by
  refine ⟨successfulCommitStage_didExecute, ?_, ?_⟩
  · intro hsafe
    cases hsafe with
    | postStateWitness _ hwitness => cases hwitness
  · intro entitled
    have hsafe := entitled.targetEvidence
    cases hsafe with
    | postStateWitness _ hwitness => cases hwitness

theorem safety_does_not_supply_discharge_receipt :
    PreservedSafety safeExecutedStage ∧
      ¬ DischargedObligation safeExecutedStage ∧
      obligationReceiptToDischargedObligation.NotEntitledFrom
        safeExecutedStage safeExecutedStage := by
  refine ⟨safeExecutedStage_preservedSafety, ?_, ?_⟩
  · intro hdischarged
    cases hdischarged with
    | receipt hreceipt => cases hreceipt
  · intro entitled
    have hdischarged := entitled.targetEvidence
    cases hdischarged with
    | receipt hreceipt => cases hreceipt

#print axioms freshTicketEntitlement
#print axioms checkedAttemptEntitlement
#print axioms commitAttemptEntitlement
#print axioms successfulExecutionEntitlement
#print axioms refusedOutcomeEntitlement
#print axioms unknownOutcomeEntitlement
#print axioms safetyEntitlement
#print axioms dischargeEntitlement
#print axioms may_attempt_not_entitled_to_commit_without_local_preconditions
#print axioms may_commit_not_entitled_to_attempt_without_send
#print axioms refused_attempt_entitled_to_refusal_not_execution
#print axioms unknown_attempt_entitled_to_neither_outcome
#print axioms execution_not_entitled_to_safety_without_witness
#print axioms safety_does_not_supply_discharge_receipt

end PJ.Instances.ExecutionCustody
