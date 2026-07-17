/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: STABLE-SURFACE

  BoundedCalculi.ExecutionCustody -- execution-stage separation calculus.
  Release-surface bounded lifecycle calculus (v3.0.0 - Bounded Lifecycle
  Calculi). Self-contained and Mathlib-free.

  RELEASE-SURFACE, NOT AUTHORITY:
    * stable substrate through the exact custody-indexed closure, without
      entering the AdmissibilityKernels root;
    * NOT a unified admissibility calculus; no master `Admissible` judgment.
    * NOT runtime authority and NOT an actuator implementation.
    * NOT sequent composition (custody-indexed sequents are a separate stable family).
    * The aggregate import (`BoundedCalculi.lean`) proves checkability /
      coexistence only.
  Historical custody: promoted Scratch -> ANNEX by operator decision
  2026-07-01; v13 recognizes its role in the stable custody-indexed closure.
  Audit trail: docs/CHANGELOG-scratch-campaign.md + .governor/loop.json.

  This is a STAGE-SEPARATION calculus: it proves the stages of execution do not
  collapse into one another (MayCommit != DidExecute, TicketSpent != DidExecute,
  DidExecute != PreservedSafety, ...). It does NOT prove real execution safety.
  Documented local-model limits: the actuator boundary is abstracted
  (`commitSent` and `outcome` are independent asserted fields, not a causal
  transition); the ticket flip is single-stage (trajectory-level linearity is
  proved in `CustodyIndexed/ExecutionSequent.lean`).

  Execution custody separates:
    MayAttempt, MayCommit, CommitAttempted, DidExecute, DidNotExecute,
    CommitUnknown, PreservedSafety, and DischargedObligation.

  Invariant: no artifact may testify beyond the execution stage it actually
  survived. A fresh ticket may permit an attempt; local preconditions may permit
  commit; a sent commit consumes the ticket; only substrate success testifies to
  execution; only a post-state safety witness testifies to safety; only an
  obligation receipt testifies to obligation discharge.
-/

namespace LeanProofs.BoundedCalculi.ExecutionCustody

/-! ## Syntax -/

inductive TicketState where
  | fresh
  | spent
  deriving DecidableEq

structure ExecutionTicket where
  id : Nat
  state : TicketState
  deriving DecidableEq

inductive SubstrateOutcome where
  | succeeded
  | refused
  | unknown
  deriving DecidableEq

structure ExecutionStage where
  preTicket : ExecutionTicket
  postTicket : ExecutionTicket
  actuatorReady : Bool
  commitWindowOpen : Bool
  commitSent : Bool
  outcome : SubstrateOutcome
  safetyWitness : Bool
  obligationReceipt : Bool
  deriving DecidableEq

def spendTicket (ticket : ExecutionTicket) : ExecutionTicket :=
  { id := ticket.id, state := TicketState.spent }

def TicketFresh (stage : ExecutionStage) : Prop :=
  stage.preTicket.state = TicketState.fresh

def TicketSpent (stage : ExecutionStage) : Prop :=
  stage.postTicket.state = TicketState.spent

def TicketConsumed (stage : ExecutionStage) : Prop :=
  stage.postTicket = spendTicket stage.preTicket

def LocalPreconditions (stage : ExecutionStage) : Prop :=
  stage.actuatorReady = true ∧ stage.commitWindowOpen = true

/-! ## Judgments -/

inductive MayAttempt : ExecutionStage → Prop where
  | freshTicket {stage : ExecutionStage} :
      TicketFresh stage →
        MayAttempt stage

inductive MayCommit : ExecutionStage → Prop where
  | checked {stage : ExecutionStage} :
      MayAttempt stage →
      LocalPreconditions stage →
        MayCommit stage

inductive CommitAttempted : ExecutionStage → Prop where
  | sent {stage : ExecutionStage} :
      MayCommit stage →
      TicketConsumed stage →
      stage.commitSent = true →
        CommitAttempted stage

inductive DidExecute : ExecutionStage → Prop where
  | substrateSuccess {stage : ExecutionStage} :
      CommitAttempted stage →
      stage.outcome = SubstrateOutcome.succeeded →
        DidExecute stage

inductive DidNotExecute : ExecutionStage → Prop where
  | substrateRefused {stage : ExecutionStage} :
      CommitAttempted stage →
      stage.outcome = SubstrateOutcome.refused →
        DidNotExecute stage

inductive CommitUnknown : ExecutionStage → Prop where
  | substrateUnknown {stage : ExecutionStage} :
      CommitAttempted stage →
      stage.outcome = SubstrateOutcome.unknown →
        CommitUnknown stage

inductive PreservedSafety : ExecutionStage → Prop where
  | postStateWitness {stage : ExecutionStage} :
      DidExecute stage →
      stage.safetyWitness = true →
        PreservedSafety stage

inductive DischargedObligation : ExecutionStage → Prop where
  | receipt {stage : ExecutionStage} :
      stage.obligationReceipt = true →
        DischargedObligation stage

/-! ## Positive rules -/

theorem fresh_ticket_may_attempt
    {stage : ExecutionStage}
    (hfresh : TicketFresh stage) :
    MayAttempt stage :=
  MayAttempt.freshTicket hfresh

theorem checked_fresh_ticket_local_preconditions_yields_mayCommit
    {stage : ExecutionStage}
    (hfresh : TicketFresh stage)
    (hlocal : LocalPreconditions stage) :
    MayCommit stage :=
  MayCommit.checked (fresh_ticket_may_attempt hfresh) hlocal

theorem successful_substrate_result_yields_didExecute
    {stage : ExecutionStage}
    (hattempt : CommitAttempted stage)
    (hsuccess : stage.outcome = SubstrateOutcome.succeeded) :
    DidExecute stage :=
  DidExecute.substrateSuccess hattempt hsuccess

theorem post_state_witness_yields_preservedSafety
    {stage : ExecutionStage}
    (hexecuted : DidExecute stage)
    (hsafe : stage.safetyWitness = true) :
    PreservedSafety stage :=
  PreservedSafety.postStateWitness hexecuted hsafe

theorem receipt_yields_dischargedObligation
    {stage : ExecutionStage}
    (hreceipt : stage.obligationReceipt = true) :
    DischargedObligation stage :=
  DischargedObligation.receipt hreceipt

/-! ## Specimens -/

def freshTicket0 : ExecutionTicket :=
  { id := 0, state := TicketState.fresh }

def spentTicket0 : ExecutionTicket :=
  spendTicket freshTicket0

def attemptOnlyStage : ExecutionStage where
  preTicket := freshTicket0
  postTicket := freshTicket0
  actuatorReady := false
  commitWindowOpen := true
  commitSent := false
  outcome := SubstrateOutcome.unknown
  safetyWitness := false
  obligationReceipt := false

def mayCommitStage : ExecutionStage where
  preTicket := freshTicket0
  postTicket := freshTicket0
  actuatorReady := true
  commitWindowOpen := true
  commitSent := false
  outcome := SubstrateOutcome.unknown
  safetyWitness := false
  obligationReceipt := false

def commitNotAttemptedStage : ExecutionStage where
  preTicket := freshTicket0
  postTicket := freshTicket0
  actuatorReady := true
  commitWindowOpen := true
  commitSent := false
  outcome := SubstrateOutcome.succeeded
  safetyWitness := false
  obligationReceipt := false

def successfulCommitStage : ExecutionStage where
  preTicket := freshTicket0
  postTicket := spentTicket0
  actuatorReady := true
  commitWindowOpen := true
  commitSent := true
  outcome := SubstrateOutcome.succeeded
  safetyWitness := false
  obligationReceipt := false

def refusedCommitStage : ExecutionStage where
  preTicket := freshTicket0
  postTicket := spentTicket0
  actuatorReady := true
  commitWindowOpen := true
  commitSent := true
  outcome := SubstrateOutcome.refused
  safetyWitness := false
  obligationReceipt := false

def unknownCommitStage : ExecutionStage where
  preTicket := freshTicket0
  postTicket := spentTicket0
  actuatorReady := true
  commitWindowOpen := true
  commitSent := true
  outcome := SubstrateOutcome.unknown
  safetyWitness := false
  obligationReceipt := false

def safeExecutedStage : ExecutionStage where
  preTicket := freshTicket0
  postTicket := spentTicket0
  actuatorReady := true
  commitWindowOpen := true
  commitSent := true
  outcome := SubstrateOutcome.succeeded
  safetyWitness := true
  obligationReceipt := false

def obligationDischargedStage : ExecutionStage where
  preTicket := freshTicket0
  postTicket := spentTicket0
  actuatorReady := true
  commitWindowOpen := true
  commitSent := true
  outcome := SubstrateOutcome.succeeded
  safetyWitness := true
  obligationReceipt := true

/-! ## Positive specimens -/

theorem mayCommitStage_mayCommit :
    MayCommit mayCommitStage :=
  checked_fresh_ticket_local_preconditions_yields_mayCommit rfl ⟨rfl, rfl⟩

theorem successfulCommitStage_mayCommit :
    MayCommit successfulCommitStage :=
  checked_fresh_ticket_local_preconditions_yields_mayCommit rfl ⟨rfl, rfl⟩

theorem successfulCommitStage_attempted :
    CommitAttempted successfulCommitStage :=
  CommitAttempted.sent successfulCommitStage_mayCommit rfl rfl

theorem successfulCommitStage_didExecute :
    DidExecute successfulCommitStage :=
  successful_substrate_result_yields_didExecute
    successfulCommitStage_attempted rfl

theorem refusedCommitStage_mayCommit :
    MayCommit refusedCommitStage :=
  checked_fresh_ticket_local_preconditions_yields_mayCommit rfl ⟨rfl, rfl⟩

theorem refusedCommitStage_attempted :
    CommitAttempted refusedCommitStage :=
  CommitAttempted.sent refusedCommitStage_mayCommit rfl rfl

theorem refusedCommitStage_didNotExecute :
    DidNotExecute refusedCommitStage :=
  DidNotExecute.substrateRefused refusedCommitStage_attempted rfl

theorem unknownCommitStage_mayCommit :
    MayCommit unknownCommitStage :=
  checked_fresh_ticket_local_preconditions_yields_mayCommit rfl ⟨rfl, rfl⟩

theorem unknownCommitStage_attempted :
    CommitAttempted unknownCommitStage :=
  CommitAttempted.sent unknownCommitStage_mayCommit rfl rfl

theorem unknownCommitStage_commitUnknown :
    CommitUnknown unknownCommitStage :=
  CommitUnknown.substrateUnknown unknownCommitStage_attempted rfl

theorem safeExecutedStage_mayCommit :
    MayCommit safeExecutedStage :=
  checked_fresh_ticket_local_preconditions_yields_mayCommit rfl ⟨rfl, rfl⟩

theorem safeExecutedStage_attempted :
    CommitAttempted safeExecutedStage :=
  CommitAttempted.sent safeExecutedStage_mayCommit rfl rfl

theorem safeExecutedStage_didExecute :
    DidExecute safeExecutedStage :=
  successful_substrate_result_yields_didExecute
    safeExecutedStage_attempted rfl

theorem safeExecutedStage_preservedSafety :
    PreservedSafety safeExecutedStage :=
  post_state_witness_yields_preservedSafety
    safeExecutedStage_didExecute rfl

theorem obligationDischargedStage_dischargedObligation :
    DischargedObligation obligationDischargedStage :=
  receipt_yields_dischargedObligation rfl

theorem commit_attempt_consumes_ticket
    {stage : ExecutionStage}
    (hattempt : CommitAttempted stage) :
    TicketSpent stage := by
  cases hattempt with
  | sent _ hconsumed _ =>
      unfold TicketSpent TicketConsumed spendTicket at *
      rw [hconsumed]

/-! ## Non-collapse theorems -/

theorem mayAttempt_does_not_imply_mayCommit :
    ∃ stage : ExecutionStage,
      MayAttempt stage ∧ ¬ MayCommit stage := by
  refine ⟨attemptOnlyStage, ?_, ?_⟩
  · exact MayAttempt.freshTicket rfl
  · intro hcommit
    cases hcommit with
    | checked _ hlocal =>
        cases hlocal.1

theorem mayCommit_does_not_imply_didExecute :
    ∃ stage : ExecutionStage,
      MayCommit stage ∧ ¬ DidExecute stage := by
  refine ⟨commitNotAttemptedStage, ?_, ?_⟩
  · exact checked_fresh_ticket_local_preconditions_yields_mayCommit rfl ⟨rfl, rfl⟩
  · intro hexec
    cases hexec with
    | substrateSuccess hattempt _ =>
        cases hattempt with
        | sent _ _ hsent =>
            cases hsent

theorem ticketSpent_does_not_imply_didExecute :
    ∃ stage : ExecutionStage,
      TicketSpent stage ∧ ¬ DidExecute stage := by
  refine ⟨refusedCommitStage, ?_, ?_⟩
  · rfl
  · intro hexec
    cases hexec with
    | substrateSuccess _ hsuccess =>
        cases hsuccess

theorem commitAttempted_does_not_imply_didExecute :
    ∃ stage : ExecutionStage,
      CommitAttempted stage ∧ ¬ DidExecute stage := by
  refine ⟨refusedCommitStage, refusedCommitStage_attempted, ?_⟩
  intro hexec
  cases hexec with
  | substrateSuccess _ hsuccess =>
      cases hsuccess

theorem didExecute_does_not_imply_preservedSafety :
    ∃ stage : ExecutionStage,
      DidExecute stage ∧ ¬ PreservedSafety stage := by
  refine ⟨successfulCommitStage, successfulCommitStage_didExecute, ?_⟩
  intro hsafe
  cases hsafe with
  | postStateWitness _ hsafety =>
      cases hsafety

theorem preservedSafety_does_not_imply_dischargedObligation :
    ∃ stage : ExecutionStage,
      PreservedSafety stage ∧ ¬ DischargedObligation stage := by
  refine ⟨safeExecutedStage, safeExecutedStage_preservedSafety, ?_⟩
  intro hdischarged
  cases hdischarged with
  | receipt hreceipt =>
      cases hreceipt

/-- Makes `CommitUnknown` load-bearing (E audit, 2026-07-01): an unknown substrate
    outcome testifies to NEITHER execution nor non-execution. Without this the
    `CommitUnknown` judgment is decorative. This is the invariant applied to the
    no-ack case: a sent commit whose outcome is unknown may not be read as success
    OR as failure. -/
theorem commitUnknown_testifies_to_neither :
    ∃ stage : ExecutionStage,
      CommitUnknown stage ∧ ¬ DidExecute stage ∧ ¬ DidNotExecute stage := by
  refine ⟨unknownCommitStage, unknownCommitStage_commitUnknown, ?_, ?_⟩
  · intro hexec
    cases hexec with
    | substrateSuccess _ hsuccess => cases hsuccess
  · intro hnexec
    cases hnexec with
    | substrateRefused _ hrefused => cases hrefused

theorem execution_custody_noncollapse_bundle :
    (∃ stage : ExecutionStage, MayAttempt stage ∧ ¬ MayCommit stage) ∧
    (∃ stage : ExecutionStage, MayCommit stage ∧ ¬ DidExecute stage) ∧
    (∃ stage : ExecutionStage, TicketSpent stage ∧ ¬ DidExecute stage) ∧
    (∃ stage : ExecutionStage, CommitAttempted stage ∧ ¬ DidExecute stage) ∧
    (∃ stage : ExecutionStage, DidExecute stage ∧ ¬ PreservedSafety stage) ∧
    (∃ stage : ExecutionStage, PreservedSafety stage ∧ ¬ DischargedObligation stage) :=
  ⟨mayAttempt_does_not_imply_mayCommit,
   mayCommit_does_not_imply_didExecute,
   ticketSpent_does_not_imply_didExecute,
   commitAttempted_does_not_imply_didExecute,
   didExecute_does_not_imply_preservedSafety,
   preservedSafety_does_not_imply_dischargedObligation⟩

end LeanProofs.BoundedCalculi.ExecutionCustody
