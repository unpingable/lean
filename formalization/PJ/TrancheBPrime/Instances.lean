/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE
-/

import PJ.TrancheBPrime.AntiMinting
import PJ.Instances.GovernedTransport
import PJ.Instances.ExecutionCustody
import PJ.Instances.ContinuityAdmission

/-!
  Faithful Tranche B-prime specializations at native PJ-A receipt boundaries.

  Each negative packet keeps source evidence and independently inhabited
  target evidence while constructively refusing the exact native receipt.
  No generic frontier, copied bridge identity, runtime conformance claim, or
  operational Continuity claim is introduced.
-/

namespace PJ.TrancheBPrime.Instances

/-! ## Governed Transport -/

namespace GovernedTransport

open LeanProofs.GovernedTransport
open LeanProofs.GovernedTransport.Hostile
open PJ.Instances.GovernedTransport

/-- Inhabited evidence families on both sides of the native incomplete span.
    They prevent the route refusal from hiding behind target falsity. -/
def SourceEvidence (_ : Unit) : Type := Unit
def TargetEvidence (_ : Bool) : Type := Unit

def translateFirst :
    TranslateAlong CompositionDebt.first SourceEvidence TargetEvidence :=
  fun _ _ => ()

/-- The frozen GT adapter binds its native receipt to the exact pullback route
    of `CompositionDebt.first`, whose only target is `false`. -/
def incompleteRouteBridge : PJ.IndexedJudgmentBridge :=
  positiveTranslationBridge translateFirst

def exactFalseEntitlement :
    incompleteRouteBridge.EntitledFrom () false where
  sourceEvidence := ()
  receipt := {
    crossing := ()
    source_eq := rfl
    target_eq := rfl
  }

/-- Source evidence and independent evidence at `true` both exist, but the
    exact native span contains no receipt from `()` to `true`. -/
theorem true_target_has_no_exact_route :
    incompleteRouteBridge.NotEntitledFrom () true := by
  intro entitlement
  have falseEqualsTrue : false = true := by
    cases entitlement.receipt.crossing
    exact entitlement.receipt.target_eq
  exact Bool.noConfusion falseEqualsTrue

/-- The repaired native span is a genuinely different bridge and does contain
    the missing exact route.  Its receipt does not inhabit the old bridge's
    receipt family. -/
def repairedRouteBridge : PJ.IndexedJudgmentBridge :=
  positiveTranslationBridge
    (bridge := CompositionDebt.repairedFirst)
    (SourcePositive := SourceEvidence)
    (ImportedPositive := TargetEvidence)
    (fun _ _ => ())

def repairedTrueEntitlement :
    repairedRouteBridge.EntitledFrom () true where
  sourceEvidence := ()
  receipt := {
    crossing := true
    source_eq := rfl
    target_eq := rfl
  }

def exactFalseConsumer :
    AdmissibleConsumer incompleteRouteBridge () false where
  Output := Unit
  consume := fun entitlement => entitlement.targetEvidence

/-- This is the faithful GT anti-minting boundary: an independently true
    target and even a different bridge that reaches it cannot mint an
    entitlement through the unrepaired bridge. -/
theorem exact_gt_route_gap_is_nonvacuous :
    Nonempty (incompleteRouteBridge.SourceJudgment ()) ∧
      Nonempty (incompleteRouteBridge.TargetJudgment true) ∧
      Nonempty (repairedRouteBridge.TargetJudgment true) ∧
      incompleteRouteBridge.NotEntitledFrom () true :=
  ⟨⟨()⟩, ⟨()⟩, ⟨repairedTrueEntitlement.targetEvidence⟩,
    true_target_has_no_exact_route⟩

/-- Exact native evidence remains sufficient on the covered target. -/
theorem exact_gt_receipt_recovers_target :
    Nonempty (incompleteRouteBridge.TargetJudgment false) :=
  ⟨exactFalseEntitlement.targetEvidence⟩

/-- A receipt-free operation for every index of this exact GT bridge would
    manufacture the missing `true` route, contradicting the native span. -/
theorem gt_route_bridge_refutes_receipt_free_mint :
    ReceiptFreeMintAt incompleteRouteBridge → False := by
  exact exact_receipt_prevents_target_minting
    (bridge := incompleteRouteBridge) (source := ()) (target := true) () ()
    true_target_has_no_exact_route

theorem exact_gt_receipt_permits_bounded_consumption :
    exactFalseConsumer.consumeEntitled exactFalseEntitlement = () := rfl

end GovernedTransport

/-! ## Execution Custody -/

namespace ExecutionCustody

open LeanProofs.BoundedCalculi.ExecutionCustody
open PJ.Instances.ExecutionCustody

/-- The source is genuinely commit-permitted and the independently chosen
    target genuinely records a committed attempt.  Their complete stages are
    different, so the native same-stage receipt is unavailable. -/
theorem different_stage_commit_receipt_is_unavailable :
    mayCommitToCommitAttempted.NotEntitledFrom
      commitNotAttemptedStage successfulCommitStage := by
  intro entitlement
  have stageEquality : commitNotAttemptedStage = successfulCommitStage :=
    entitlement.receipt.sameStage
  have sentEquality : false = true :=
    congrArg ExecutionStage.commitSent stageEquality
  cases sentEquality

/-- Permission and committed-attempt truth remain inhabited on their own
    exact stages; neither fact changes the missing cross-stage receipt. -/
theorem permission_does_not_mint_committed_attempt :
    MayCommit commitNotAttemptedStage ∧
      CommitAttempted successfulCommitStage ∧
      mayCommitToCommitAttempted.NotEntitledFrom
        commitNotAttemptedStage successfulCommitStage :=
  ⟨checked_fresh_ticket_local_preconditions_yields_mayCommit
      rfl ⟨rfl, rfl⟩,
    successfulCommitStage_attempted,
    different_stage_commit_receipt_is_unavailable⟩

/-- The stronger native same-stage wall remains intact: permission without
    ticket consumption and an actual send supplies neither attempt nor
    execution entitlement.  The cross-stage packet above is the separate
    non-vacuity hostile where the target judgment is independently true. -/
theorem same_stage_permission_without_send_remains_not_entitled :
    MayCommit commitNotAttemptedStage ∧
      ¬ CommitAttempted commitNotAttemptedStage ∧
      ¬ DidExecute commitNotAttemptedStage ∧
      mayCommitToCommitAttempted.NotEntitledFrom
        commitNotAttemptedStage commitNotAttemptedStage :=
  may_commit_not_entitled_to_attempt_without_send

/-- The exact same-stage receipt remains sufficient for the bounded native
    constructor edge. -/
theorem exact_execution_receipt_recovers_attempt :
    CommitAttempted successfulCommitStage :=
  commitAttemptEntitlement.targetEvidence

/-- B-prime does not collapse the source calculus's three outcome lanes. -/
theorem unknown_execution_outcomes_remain_distinct :
    CommitUnknown unknownCommitStage ∧
      ¬ DidExecute unknownCommitStage ∧
      ¬ DidNotExecute unknownCommitStage :=
  ⟨unknown_attempt_entitled_to_neither_outcome.1,
    unknown_attempt_entitled_to_neither_outcome.2.1,
    unknown_attempt_entitled_to_neither_outcome.2.2.1⟩

structure AttemptObservation : Type where
  evidence : CommitAttempted successfulCommitStage

def exactAttemptConsumer :
    AdmissibleConsumer mayCommitToCommitAttempted
      successfulCommitStage successfulCommitStage where
  Output := AttemptObservation
  consume := fun entitlement => ⟨entitlement.targetEvidence⟩

/-- A receipt-free operation for this native constructor edge would conflate
    two different complete execution stages. -/
theorem execution_bridge_refutes_receipt_free_mint :
    ReceiptFreeMintAt mayCommitToCommitAttempted → False := by
  exact exact_receipt_prevents_target_minting
    (bridge := mayCommitToCommitAttempted)
    (source := commitNotAttemptedStage) (target := successfulCommitStage)
    permission_does_not_mint_committed_attempt.1
    successfulCommitStage_attempted
    different_stage_commit_receipt_is_unavailable

theorem exact_execution_receipt_permits_bounded_consumption :
    CommitAttempted successfulCommitStage :=
  (exactAttemptConsumer.consumeEntitled commitAttemptEntitlement).evidence

end ExecutionCustody

/-! ## Someone Continuity -/

namespace ContinuityAdmission

open Continuity.Admission
open PJ.Instances.ContinuityAdmission

/-- Reachability cannot cross the exact asserted `AgentId` boundary. -/
theorem cross_agent_receipt_is_unavailable :
    ownsPacketBridge.NotEntitledFrom
      (initial johnId) (initial gwenId) := by
  intro entitlement
  have differentIds : gwenId ≠ johnId := by decide
  exact differentIds (receipt_preserves_agent_id entitlement.receipt)

/-- Both initial agents satisfy the ownership invariant.  Gwen's local packet
    truth does not mint a John-relative continuity receipt. -/
theorem packet_truth_does_not_mint_cross_agent_continuity :
    OwnsPacket (initial johnId) ∧
      OwnsPacket (initial gwenId) ∧
      ownsPacketBridge.NotEntitledFrom
        (initial johnId) (initial gwenId) :=
  ⟨initial_owns johnId, initial_owns gwenId,
    cross_agent_receipt_is_unavailable⟩

/-- The exact native admission route remains sufficient within John's own
    reachable fragment. -/
theorem exact_continuity_receipt_recovers_ownership :
    OwnsPacket
      ⟨johnId, targetState (acceptedPacket johnAdmission),
        some (acceptedPacket johnAdmission)⟩ :=
  (ownPacketOwnershipEntitlement johnId johnAdmission rfl).targetEvidence

structure PacketObservation : Type where
  evidence :
    OwnsPacket
      ⟨johnId, targetState (acceptedPacket johnAdmission),
        some (acceptedPacket johnAdmission)⟩

def exactContinuityConsumer :
    AdmissibleConsumer ownsPacketBridge
      (initial johnId)
      ⟨johnId, targetState (acceptedPacket johnAdmission),
        some (acceptedPacket johnAdmission)⟩ where
  Output := PacketObservation
  consume := fun entitlement => ⟨entitlement.targetEvidence⟩

/-- A receipt-free operation for the native reachable-fragment bridge would
    manufacture cross-agent continuity from two local ownership truths. -/
theorem continuity_bridge_refutes_receipt_free_mint :
    ReceiptFreeMintAt ownsPacketBridge → False := by
  exact exact_receipt_prevents_target_minting
    (bridge := ownsPacketBridge)
    (source := initial johnId) (target := initial gwenId)
    (initial_owns johnId) (initial_owns gwenId)
    cross_agent_receipt_is_unavailable

theorem exact_continuity_receipt_permits_bounded_consumption :
    OwnsPacket
      ⟨johnId, targetState (acceptedPacket johnAdmission),
        some (acceptedPacket johnAdmission)⟩ :=
  (exactContinuityConsumer.consumeEntitled
    (ownPacketOwnershipEntitlement johnId johnAdmission rfl)).evidence

end ContinuityAdmission

#print axioms GovernedTransport.true_target_has_no_exact_route
#print axioms GovernedTransport.exact_gt_route_gap_is_nonvacuous
#print axioms GovernedTransport.exact_gt_receipt_recovers_target
#print axioms GovernedTransport.gt_route_bridge_refutes_receipt_free_mint
#print axioms GovernedTransport.exact_gt_receipt_permits_bounded_consumption
#print axioms ExecutionCustody.different_stage_commit_receipt_is_unavailable
#print axioms ExecutionCustody.permission_does_not_mint_committed_attempt
#print axioms ExecutionCustody.same_stage_permission_without_send_remains_not_entitled
#print axioms ExecutionCustody.exact_execution_receipt_recovers_attempt
#print axioms ExecutionCustody.unknown_execution_outcomes_remain_distinct
#print axioms ExecutionCustody.execution_bridge_refutes_receipt_free_mint
#print axioms ExecutionCustody.exact_execution_receipt_permits_bounded_consumption
#print axioms ContinuityAdmission.cross_agent_receipt_is_unavailable
#print axioms ContinuityAdmission.packet_truth_does_not_mint_cross_agent_continuity
#print axioms ContinuityAdmission.exact_continuity_receipt_recovers_ownership
#print axioms ContinuityAdmission.continuity_bridge_refutes_receipt_free_mint
#print axioms ContinuityAdmission.exact_continuity_receipt_permits_bounded_consumption

end PJ.TrancheBPrime.Instances
