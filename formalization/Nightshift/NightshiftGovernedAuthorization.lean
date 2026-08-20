/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE
-/

/-
  NightshiftGovernedAuthorization

  Source contract: nightshift/docs/CANONICAL_RUNTIME_C1.md
  Formalization handoff:
    nightshift/docs/working/decisions/FORMALIZATION-HANDOFF.md

  F1 only: a small safety model of the governed AG authorization boundary.
  This formalization describes the frozen runtime contract. External truth
  assumptions remain environmental; no end-to-end world-truth theorem is
  claimed.
  The authority boundary stops at the one-use AG spend; Docket execution and
  real-world effect are outside this model. Observation usability, current
  workflow judgment, and standing are present-tense environmental inputs.
  Their truthfulness and the cryptographic realization of work identities are
  not proved here.

  `SpendOccurs` models a successful canonical `CampaignEngineV1::authorize`
  transition through its atomic authoritative-store commit. It does not model
  an uncommitted pure-kernel candidate or an arbitrary caller of the lower-level
  generic store API. Exact AG work is checked when the proposal is recorded and
  then preserved as a reachable-state invariant; unlike the four environmental
  judgments, it is not modeled as a fresh resolver input at authorization.

  The environment relation is a deliberate conservative over-approximation.
  It permits usability to recover even where concrete Stale/Superseded states
  are monotone, permits usability and basis to vary independently although one
  resolver supplies both, and permits basis values to revert. Every F1 theorem
  is state-local and assumes no environment monotonicity; in particular, F1
  does not prove permanent unusability after supersession.

  A committed spend records the observation, standing, and admission judgments
  accepted by that authorize operation. This does not freeze external reality
  between resolver reads and SQLite commit, assert standing truth at the commit
  nanosecond, or keep any gate true after spend. The concrete gap is controlled
  by freshness windows and state-digest/CAS commit discipline.
-/

import ObservationAdequacy.Basic

namespace NightshiftGovernedAuthorization

universe uBasis uWork

/-! ## Authority-relevant state -/

/-- `awaitingProposal` is the local pre-recording setup point. The other
constructors are the three authority-relevant C1 program counters. -/
inductive ProgramCounter where
  | awaitingProposal
  | proposalRecorded
  | admissiblePendingAuthorization
  | authorizationConsumed
  deriving DecidableEq, Repr

/-- AG-side proposal data. Nightshift's compiled-work identity is a distinct
domain and is intentionally outside F1; this model compares only the AG
proposal work with the occurrence's AG expected work. -/
structure ProposalData (BasisRef : Type uBasis) (AgWork : Type uWork) where
  recordedBasis : BasisRef
  proposalWork : AgWork
  expectedWork : AgWork

/-- Present-tense inputs re-read by AG. The Boolean fields abstract resolver,
catalog, and standing results; `currentBasis` remains an abstract identity. -/
structure Environment (BasisRef : Type uBasis) where
  observationUsable : Bool
  currentBasis : BasisRef
  workflowAllowed : Bool
  standing : Bool

structure GovernedState (BasisRef : Type uBasis) (AgWork : Type uWork) where
  pc : ProgramCounter
  proposal : ProposalData BasisRef AgWork
  environment : Environment BasisRef
  spendCount : Nat

namespace GovernedState

variable {BasisRef : Type uBasis} {AgWork : Type uWork}

def afterRecord (state : GovernedState BasisRef AgWork) :
    GovernedState BasisRef AgWork :=
  { state with pc := .proposalRecorded }

def afterDecide (state : GovernedState BasisRef AgWork) :
    GovernedState BasisRef AgWork :=
  { state with pc := .admissiblePendingAuthorization }

def afterAuthorize (state : GovernedState BasisRef AgWork) :
    GovernedState BasisRef AgWork :=
  { state with pc := .authorizationConsumed, spendCount := 1 }

def withEnvironment (state : GovernedState BasisRef AgWork)
    (environment : Environment BasisRef) : GovernedState BasisRef AgWork :=
  { state with environment := environment }

end GovernedState

namespace Environment

variable {BasisRef : Type uBasis}

def withStanding (environment : Environment BasisRef) (standing : Bool) :
    Environment BasisRef :=
  { environment with standing := standing }

def withCurrentBasis (environment : Environment BasisRef)
    (basis : BasisRef) : Environment BasisRef :=
  { environment with currentBasis := basis }

def withWorkflowAllowed (environment : Environment BasisRef)
    (allowed : Bool) : Environment BasisRef :=
  { environment with workflowAllowed := allowed }

end Environment

/-- The four present-tense environmental judgments re-read before spend. -/
def CurrentAuthorizationGates {BasisRef : Type uBasis} {AgWork : Type uWork}
    (state : GovernedState BasisRef AgWork) : Prop :=
  state.environment.observationUsable = true ∧
    state.environment.currentBasis = state.proposal.recordedBasis ∧
    state.environment.workflowAllowed = true ∧
    state.environment.standing = true

/-- All five F1 non-ledger authorization conditions at the pre-spend state.
The work equality is a preserved record-time integrity invariant, not a live
environmental judgment. -/
def AuthorizationGates {BasisRef : Type uBasis} {AgWork : Type uWork}
    (state : GovernedState BasisRef AgWork) : Prop :=
  CurrentAuthorizationGates state ∧
    state.proposal.proposalWork = state.proposal.expectedWork

/-! ## Explicit transition relation -/

inductive Action (BasisRef : Type uBasis) where
  | recordProposal
  | decide
  | authorize
  | changeEnvironment (next : Environment BasisRef)

/-- The only constructor that increments the spend ledger is `authorize`.
Environment changes preserve the immutable proposal and its pinned basis.
They intentionally over-approximate concrete resolver evolution as described
in the module header; the safety theorems require no monotonicity. -/
inductive GovernedStep {BasisRef : Type uBasis} {AgWork : Type uWork} :
    GovernedState BasisRef AgWork → Action BasisRef →
      GovernedState BasisRef AgWork → Prop where
  /-- The concrete runtime first establishes exact-work binding, then freshly
  resolves the cited observation and pins its returned basis. These observation
  and basis premises are intentional record-time correspondence. -/
  | recordProposal (state : GovernedState BasisRef AgWork)
      (atBoundary : state.pc = .awaitingProposal)
      (observationUsable : state.environment.observationUsable = true)
      (basisPinned :
        state.environment.currentBasis = state.proposal.recordedBasis)
      (workBound :
        state.proposal.proposalWork = state.proposal.expectedWork) :
      GovernedStep state .recordProposal state.afterRecord
  | decide (state : GovernedState BasisRef AgWork)
      (proposalRecorded : state.pc = .proposalRecorded)
      (gates : CurrentAuthorizationGates state) :
      GovernedStep state .decide state.afterDecide
  | authorize (state : GovernedState BasisRef AgWork)
      (admissible : state.pc = .admissiblePendingAuthorization)
      (gates : CurrentAuthorizationGates state)
      (unused : state.spendCount = 0) :
      GovernedStep state .authorize state.afterAuthorize
  | changeEnvironment (state : GovernedState BasisRef AgWork)
      (next : Environment BasisRef) :
      GovernedStep state (.changeEnvironment next) (state.withEnvironment next)

def system (BasisRef : Type uBasis) (AgWork : Type uWork) :
    ObservationAdequacy.RelSystem
      (GovernedState BasisRef AgWork) (Action BasisRef) :=
  ⟨GovernedStep⟩

/-- One successfully committed authorization transition in the canonical
engine history. Its durable spend artifact records the judgments accepted by
this operation; the definition makes no claim that their external referents
remain true before, at, or after the commit instant. -/
def SpendOccurs {BasisRef : Type uBasis} {AgWork : Type uWork}
    (before after : GovernedState BasisRef AgWork) : Prop :=
  (system BasisRef AgWork).Step before .authorize after

/-! ## F1 gate theorems -/

/-- Every spend constructor carries the four present-tense gate judgments from
its pre-spend state. The record-time work invariant is added to the reachable
T1 theorem below. -/
theorem spend_implies_current_authorization_gates
    {BasisRef : Type uBasis} {AgWork : Type uWork}
    {before after : GovernedState BasisRef AgWork}
    (spend : SpendOccurs before after) :
    before.environment.observationUsable = true ∧
      before.environment.currentBasis = before.proposal.recordedBasis ∧
      before.environment.workflowAllowed = true ∧
      before.environment.standing = true := by
  change GovernedStep before .authorize after at spend
  cases spend with
  | authorize _ gates _ => exact gates

/-- The authorize transition is the minting event: it moves to the consumed
counter and records exactly the occurrence's first spend. -/
theorem authorization_transition_mints_one_spend
    {BasisRef : Type uBasis} {AgWork : Type uWork}
    {before after : GovernedState BasisRef AgWork}
    (spend : SpendOccurs before after) :
    before.spendCount = 0 ∧
      after.pc = .authorizationConsumed ∧ after.spendCount = 1 := by
  change GovernedStep before .authorize after at spend
  cases spend with
  | authorize _ _ unused => exact ⟨unused, rfl, rfl⟩

theorem workflow_refusal_prevents_spend
    {BasisRef : Type uBasis} {AgWork : Type uWork}
    {before after : GovernedState BasisRef AgWork}
    (refused : before.environment.workflowAllowed = false) :
    ¬ SpendOccurs before after := by
  intro spend
  have allowed := (spend_implies_current_authorization_gates spend).2.2.1
  rw [refused] at allowed
  contradiction

/-- T4: a closed present-tense standing gate disables the spend transition. -/
theorem closed_standing_prevents_spend
    {BasisRef : Type uBasis} {AgWork : Type uWork}
    {before after : GovernedState BasisRef AgWork}
    (closed : before.environment.standing = false) :
    ¬ SpendOccurs before after := by
  intro spend
  have standingOpen := (spend_implies_current_authorization_gates spend).2.2.2
  rw [closed] at standingOpen
  contradiction

/-- T5: a changed current basis cannot refresh or spend the old proposal. -/
theorem changed_evidence_basis_prevents_spend
    {BasisRef : Type uBasis} {AgWork : Type uWork}
    {before after : GovernedState BasisRef AgWork}
    (changed :
      before.environment.currentBasis ≠ before.proposal.recordedBasis) :
    ¬ SpendOccurs before after := by
  intro spend
  exact changed (spend_implies_current_authorization_gates spend).2.1

/-! ## Inertness and reachability discipline -/

def Initial {BasisRef : Type uBasis} {AgWork : Type uWork}
    (state : GovernedState BasisRef AgWork) : Prop :=
  state.pc = .awaitingProposal ∧ state.spendCount = 0

def Reachable {BasisRef : Type uBasis} {AgWork : Type uWork}
    (state : GovernedState BasisRef AgWork) : Prop :=
  ∃ initial,
    Initial initial ∧ (system BasisRef AgWork).Reachable initial state

theorem initial_is_reachable
    {BasisRef : Type uBasis} {AgWork : Type uWork}
    {state : GovernedState BasisRef AgWork}
    (initial : Initial state) : Reachable state :=
  ⟨state, initial, (system BasisRef AgWork).initial_reachable state⟩

theorem reachable_after_step
    {BasisRef : Type uBasis} {AgWork : Type uWork}
    {before after : GovernedState BasisRef AgWork}
    {action : Action BasisRef}
    (reachable : Reachable before)
    (step : (system BasisRef AgWork).Step before action after) :
    Reachable after := by
  rcases reachable with ⟨initial, initialState, history⟩
  exact ⟨initial, initialState,
    (system BasisRef AgWork).reachable_step history step⟩

/-- The ledger and control point agree: only `AuthorizationConsumed` carries
one spend, and every earlier modeled point carries zero. -/
def SpendDiscipline {BasisRef : Type uBasis} {AgWork : Type uWork}
    (state : GovernedState BasisRef AgWork) : Prop :=
  (state.pc = .authorizationConsumed → state.spendCount = 1) ∧
    (state.pc ≠ .authorizationConsumed → state.spendCount = 0)

/-- Once recording has succeeded, the immutable AG-side work equality stays
established throughout the modeled occurrence. -/
def WorkDiscipline {BasisRef : Type uBasis} {AgWork : Type uWork}
    (state : GovernedState BasisRef AgWork) : Prop :=
  state.pc = .awaitingProposal ∨
    state.proposal.proposalWork = state.proposal.expectedWork

theorem initial_spend_discipline
    {BasisRef : Type uBasis} {AgWork : Type uWork}
    {state : GovernedState BasisRef AgWork}
    (initial : Initial state) : SpendDiscipline state := by
  constructor
  · intro consumed
    rw [initial.1] at consumed
    contradiction
  · intro _
    exact initial.2

theorem initial_work_discipline
    {BasisRef : Type uBasis} {AgWork : Type uWork}
    {state : GovernedState BasisRef AgWork}
    (initial : Initial state) : WorkDiscipline state :=
  Or.inl initial.1

theorem step_preserves_spend_discipline
    {BasisRef : Type uBasis} {AgWork : Type uWork}
    {before after : GovernedState BasisRef AgWork}
    {action : Action BasisRef}
    (discipline : SpendDiscipline before)
    (step : (system BasisRef AgWork).Step before action after) :
    SpendDiscipline after := by
  change GovernedStep before action after at step
  cases step with
  | recordProposal atBoundary _ _ _ =>
      have unspent : before.spendCount = 0 := discipline.2 (by
        intro consumed
        rw [atBoundary] at consumed
        contradiction)
      exact ⟨by intro consumed; contradiction, by
        intro _
        exact unspent⟩
  | decide proposalRecorded _ =>
      have unspent : before.spendCount = 0 := discipline.2 (by
        intro consumed
        rw [proposalRecorded] at consumed
        contradiction)
      exact ⟨by intro consumed; contradiction, by
        intro _
        exact unspent⟩
  | authorize =>
      exact ⟨fun _ => rfl, fun notConsumed => False.elim (notConsumed rfl)⟩
  | changeEnvironment _ =>
      exact discipline

theorem step_preserves_work_discipline
    {BasisRef : Type uBasis} {AgWork : Type uWork}
    {before after : GovernedState BasisRef AgWork}
    {action : Action BasisRef}
    (discipline : WorkDiscipline before)
    (step : (system BasisRef AgWork).Step before action after) :
    WorkDiscipline after := by
  change GovernedStep before action after at step
  cases step with
  | recordProposal _ _ _ workBound => exact Or.inr workBound
  | decide proposalRecorded _ =>
      exact Or.inr (discipline.resolve_left (by
        intro awaiting
        rw [proposalRecorded] at awaiting
        contradiction))
  | authorize admissible _ _ =>
      exact Or.inr (discipline.resolve_left (by
        intro awaiting
        rw [admissible] at awaiting
        contradiction))
  | changeEnvironment => exact discipline

theorem runs_preserve_disciplines
    {BasisRef : Type uBasis} {AgWork : Type uWork}
    {start finish : GovernedState BasisRef AgWork}
    {actions : List (Action BasisRef)}
    (runs : (system BasisRef AgWork).Runs start actions finish)
    (spendDiscipline : SpendDiscipline start)
    (workDiscipline : WorkDiscipline start) :
    SpendDiscipline finish ∧ WorkDiscipline finish := by
  induction runs with
  | nil => exact ⟨spendDiscipline, workDiscipline⟩
  | cons step _ inductionHypothesis =>
      exact inductionHypothesis
        (step_preserves_spend_discipline spendDiscipline step)
        (step_preserves_work_discipline workDiscipline step)

theorem reachable_disciplines
    {BasisRef : Type uBasis} {AgWork : Type uWork}
    {state : GovernedState BasisRef AgWork}
    (reachable : Reachable state) :
    SpendDiscipline state ∧ WorkDiscipline state := by
  rcases reachable with ⟨initial, initialState, actions, runs⟩
  exact runs_preserve_disciplines runs
    (initial_spend_discipline initialState)
    (initial_work_discipline initialState)

/-- T2: a valid reachable `ProposalRecorded` state has no spend. -/
theorem proposal_recorded_is_inert
    {BasisRef : Type uBasis} {AgWork : Type uWork}
    {state : GovernedState BasisRef AgWork}
    (reachable : Reachable state)
    (recorded : state.pc = .proposalRecorded) :
    state.spendCount = 0 := by
  exact (reachable_disciplines reachable).1.2 (by
    intro consumed
    rw [recorded] at consumed
    contradiction)

/-- T3: a valid reachable `AdmissiblePendingAuthorization` state still has
no spend. -/
theorem admissibility_is_inert
    {BasisRef : Type uBasis} {AgWork : Type uWork}
    {state : GovernedState BasisRef AgWork}
    (reachable : Reachable state)
    (admissible : state.pc = .admissiblePendingAuthorization) :
    state.spendCount = 0 := by
  exact (reachable_disciplines reachable).1.2 (by
    intro consumed
    rw [admissible] at consumed
    contradiction)

theorem record_proposal_does_not_mint_spend
    {BasisRef : Type uBasis} {AgWork : Type uWork}
    {before after : GovernedState BasisRef AgWork}
    (step :
      (system BasisRef AgWork).Step before .recordProposal after) :
    after.spendCount = before.spendCount := by
  change GovernedStep before .recordProposal after at step
  cases step
  rfl

theorem admissibility_does_not_mint_spend
    {BasisRef : Type uBasis} {AgWork : Type uWork}
    {before after : GovernedState BasisRef AgWork}
    (step : (system BasisRef AgWork).Step before .decide after) :
    after.spendCount = before.spendCount := by
  change GovernedStep before .decide after at step
  cases step
  rfl

theorem environment_change_does_not_mint_spend
    {BasisRef : Type uBasis} {AgWork : Type uWork}
    {before after : GovernedState BasisRef AgWork}
    {next : Environment BasisRef}
    (step :
      (system BasisRef AgWork).Step before (.changeEnvironment next) after) :
    after.spendCount = before.spendCount := by
  change GovernedStep before (.changeEnvironment next) after at step
  cases step
  rfl

theorem every_step_preserves_proposal
    {BasisRef : Type uBasis} {AgWork : Type uWork}
    {before after : GovernedState BasisRef AgWork}
    {action : Action BasisRef}
    (step : (system BasisRef AgWork).Step before action after) :
    after.proposal = before.proposal := by
  change GovernedStep before action after at step
  cases step <;> rfl

/-- T7: every reachable state in one modeled occurrence's linear,
authoritatively committed history contains at most one spend. The occurrence
is the runtime `(campaign_id, occurrence_id)` unit; uncommitted candidates and
distributed-store semantics are outside this narrow claim. -/
theorem one_occurrence_cannot_mint_two_spends
    {BasisRef : Type uBasis} {AgWork : Type uWork}
    {state : GovernedState BasisRef AgWork}
    (reachable : Reachable state) : state.spendCount ≤ 1 := by
  by_cases consumed : state.pc = .authorizationConsumed
  · rw [(reachable_disciplines reachable).1.1 consumed]
    exact Nat.le_refl 1
  · rw [(reachable_disciplines reachable).1.2 consumed]
    exact Nat.zero_le 1

theorem authorization_consumed_cannot_spend_again
    {BasisRef : Type uBasis} {AgWork : Type uWork}
    {before : GovernedState BasisRef AgWork}
    (consumed : before.pc = .authorizationConsumed) :
    ∀ after, ¬ SpendOccurs before after := by
  intro after spend
  change GovernedStep before .authorize after at spend
  cases spend with
  | authorize admissible _ _ =>
      rw [consumed] at admissible
      contradiction

/-- Reachable proposal/admissibility states preserve the record-time work
binding, rather than classifying mismatch as workflow policy. -/
theorem reachable_recorded_work_is_bound
    {BasisRef : Type uBasis} {AgWork : Type uWork}
    {state : GovernedState BasisRef AgWork}
    (reachable : Reachable state)
    (pastRecordBoundary : state.pc ≠ .awaitingProposal) :
    state.proposal.proposalWork = state.proposal.expectedWork :=
  (reachable_disciplines reachable).2.resolve_left pastRecordBoundary

/-- T1: a spend in the canonical reachable history implies all four fresh
environmental judgments and the preserved exact-work binding in its
authorize-time pre-state. -/
theorem spend_implies_authorization_gates
    {BasisRef : Type uBasis} {AgWork : Type uWork}
    {before after : GovernedState BasisRef AgWork}
    (reachable : Reachable before)
    (spend : SpendOccurs before after) : AuthorizationGates before := by
  have current := spend_implies_current_authorization_gates spend
  have admissible : before.pc = .admissiblePendingAuthorization := by
    change GovernedStep before .authorize after at spend
    cases spend with
    | authorize atBoundary _ _ => exact atBoundary
  have workBound := reachable_recorded_work_is_bound reachable (by
    intro awaiting
    rw [admissible] at awaiting
    contradiction)
  exact ⟨current, workBound⟩

/-- T6: a work mismatch cannot occur at a spend boundary in the canonical
reachable history because recording established and preserved exact binding. -/
theorem work_mismatch_prevents_spend
    {BasisRef : Type uBasis} {AgWork : Type uWork}
    {before after : GovernedState BasisRef AgWork}
    (reachable : Reachable before)
    (mismatch :
      before.proposal.proposalWork ≠ before.proposal.expectedWork) :
    ¬ SpendOccurs before after := by
  intro spend
  exact mismatch (spend_implies_authorization_gates reachable spend).2

theorem work_mismatch_prevents_recording
    {BasisRef : Type uBasis} {AgWork : Type uWork}
    {before after : GovernedState BasisRef AgWork}
    (mismatch :
      before.proposal.proposalWork ≠ before.proposal.expectedWork) :
    ¬ (system BasisRef AgWork).Step before .recordProposal after := by
  intro step
  change GovernedStep before .recordProposal after at step
  cases step with
  | recordProposal _ _ _ workBound => exact mismatch workBound

/-! ## Required C1 trace witnesses -/

theorem record_proposal_permits_workflow_refusal
    {BasisRef : Type uBasis} {AgWork : Type uWork}
    (state : GovernedState BasisRef AgWork)
    (atBoundary : state.pc = .awaitingProposal)
    (observationUsable : state.environment.observationUsable = true)
    (basisPinned :
      state.environment.currentBasis = state.proposal.recordedBasis)
    (workBound :
      state.proposal.proposalWork = state.proposal.expectedWork)
    (refused : state.environment.workflowAllowed = false) :
    (system BasisRef AgWork).Step state .recordProposal state.afterRecord ∧
      state.afterRecord.pc = .proposalRecorded ∧
      state.afterRecord.environment.workflowAllowed = false ∧
      state.afterRecord.spendCount = state.spendCount := by
  exact ⟨.recordProposal state atBoundary observationUsable basisPinned workBound,
    rfl, refused, rfl⟩

theorem record_proposal_permits_absent_standing
    {BasisRef : Type uBasis} {AgWork : Type uWork}
    (state : GovernedState BasisRef AgWork)
    (atBoundary : state.pc = .awaitingProposal)
    (observationUsable : state.environment.observationUsable = true)
    (basisPinned :
      state.environment.currentBasis = state.proposal.recordedBasis)
    (workBound :
      state.proposal.proposalWork = state.proposal.expectedWork)
    (absent : state.environment.standing = false) :
    (system BasisRef AgWork).Step state .recordProposal state.afterRecord ∧
      state.afterRecord.pc = .proposalRecorded ∧
      state.afterRecord.environment.standing = false ∧
      state.afterRecord.spendCount = state.spendCount := by
  exact ⟨.recordProposal state atBoundary observationUsable basisPinned workBound,
    rfl, absent, rfl⟩

theorem environment_change_preserves_occurrence
    {BasisRef : Type uBasis} {AgWork : Type uWork}
    (state : GovernedState BasisRef AgWork)
    (next : Environment BasisRef) :
    (system BasisRef AgWork).Step state (.changeEnvironment next)
        (state.withEnvironment next) ∧
      (state.withEnvironment next).pc = state.pc ∧
      (state.withEnvironment next).proposal = state.proposal ∧
      (state.withEnvironment next).spendCount = state.spendCount := by
  exact ⟨.changeEnvironment state next, rfl, rfl, rfl⟩

theorem standing_recovery_without_new_proposal
    {BasisRef : Type uBasis} {AgWork : Type uWork}
    (state : GovernedState BasisRef AgWork)
    (absent : state.environment.standing = false) :
    let recovered := state.withEnvironment
      (state.environment.withStanding true)
    (system BasisRef AgWork).Step state
        (.changeEnvironment (state.environment.withStanding true)) recovered ∧
      recovered.pc = state.pc ∧
      recovered.proposal = state.proposal ∧
      state.environment.standing = false ∧
      recovered.environment.standing = true := by
  exact ⟨.changeEnvironment state _, rfl, rfl, absent, rfl⟩

theorem evidence_change_does_not_refresh_recorded_basis
    {BasisRef : Type uBasis} {AgWork : Type uWork}
    (state : GovernedState BasisRef AgWork) (nextBasis : BasisRef) :
    let changed := state.withEnvironment
      (state.environment.withCurrentBasis nextBasis)
    (system BasisRef AgWork).Step state
        (.changeEnvironment
          (state.environment.withCurrentBasis nextBasis)) changed ∧
      changed.proposal.recordedBasis = state.proposal.recordedBasis ∧
      changed.environment.currentBasis = nextBasis := by
  exact ⟨.changeEnvironment state _, rfl, rfl⟩

theorem changed_evidence_before_authorization_prevents_spend
    {BasisRef : Type uBasis} {AgWork : Type uWork}
    (state : GovernedState BasisRef AgWork) (nextBasis : BasisRef)
    (different : nextBasis ≠ state.proposal.recordedBasis) :
    let changed := state.withEnvironment
      (state.environment.withCurrentBasis nextBasis)
    (system BasisRef AgWork).Step state
        (.changeEnvironment
          (state.environment.withCurrentBasis nextBasis)) changed ∧
      changed.proposal.recordedBasis = state.proposal.recordedBasis ∧
      ∀ after, ¬ SpendOccurs changed after := by
  refine ⟨.changeEnvironment state _, rfl, ?_⟩
  intro after
  exact changed_evidence_basis_prevents_spend (before :=
    state.withEnvironment (state.environment.withCurrentBasis nextBasis))
    (by exact different)

theorem current_workflow_policy_may_change
    {BasisRef : Type uBasis} {AgWork : Type uWork}
    (state : GovernedState BasisRef AgWork) (allowed : Bool) :
    let changed := state.withEnvironment
      (state.environment.withWorkflowAllowed allowed)
    (system BasisRef AgWork).Step state
        (.changeEnvironment
          (state.environment.withWorkflowAllowed allowed)) changed ∧
      changed.pc = state.pc ∧
      changed.proposal = state.proposal ∧
      changed.environment.workflowAllowed = allowed := by
  exact ⟨.changeEnvironment state _, rfl, rfl, rfl⟩

theorem tightened_workflow_policy_prevents_spend
    {BasisRef : Type uBasis} {AgWork : Type uWork}
    (state : GovernedState BasisRef AgWork)
    (wasAllowed : state.environment.workflowAllowed = true) :
    let tightened := state.withEnvironment
      (state.environment.withWorkflowAllowed false)
    (system BasisRef AgWork).Step state
        (.changeEnvironment
          (state.environment.withWorkflowAllowed false)) tightened ∧
      state.environment.workflowAllowed = true ∧
      ∀ after, ¬ SpendOccurs tightened after := by
  refine ⟨.changeEnvironment state _, wasAllowed, ?_⟩
  intro after
  exact workflow_refusal_prevents_spend (before :=
    state.withEnvironment (state.environment.withWorkflowAllowed false)) rfl

theorem recovered_standing_can_authorize
    {BasisRef : Type uBasis} {AgWork : Type uWork}
    (state : GovernedState BasisRef AgWork)
    (admissible : state.pc = .admissiblePendingAuthorization)
    (observationUsable : state.environment.observationUsable = true)
    (basisPinned :
      state.environment.currentBasis = state.proposal.recordedBasis)
    (workflowAllowed : state.environment.workflowAllowed = true)
    (workBound :
      state.proposal.proposalWork = state.proposal.expectedWork)
    (absent : state.environment.standing = false)
    (unused : state.spendCount = 0) :
    let recovered := state.withEnvironment
      (state.environment.withStanding true)
    let spent := recovered.afterAuthorize
    state.environment.standing = false ∧
      (system BasisRef AgWork).Runs state
          [.changeEnvironment (state.environment.withStanding true), .authorize]
          spent ∧
        spent.spendCount = 1 ∧
        spent.proposal.proposalWork = spent.proposal.expectedWork := by
  let recovered := state.withEnvironment
    (state.environment.withStanding true)
  have gates : CurrentAuthorizationGates recovered :=
    ⟨observationUsable, basisPinned, workflowAllowed, rfl⟩
  exact ⟨absent, .cons (.changeEnvironment state _)
      (.cons (.authorize recovered admissible gates unused) (.nil _)), rfl, workBound⟩

theorem loosened_workflow_policy_can_authorize
    {BasisRef : Type uBasis} {AgWork : Type uWork}
    (state : GovernedState BasisRef AgWork)
    (admissible : state.pc = .admissiblePendingAuthorization)
    (observationUsable : state.environment.observationUsable = true)
    (basisPinned :
      state.environment.currentBasis = state.proposal.recordedBasis)
    (refused : state.environment.workflowAllowed = false)
    (standing : state.environment.standing = true)
    (workBound :
      state.proposal.proposalWork = state.proposal.expectedWork)
    (unused : state.spendCount = 0) :
    let loosened := state.withEnvironment
      (state.environment.withWorkflowAllowed true)
    let spent := loosened.afterAuthorize
    state.environment.workflowAllowed = false ∧
      (system BasisRef AgWork).Runs state
          [.changeEnvironment (state.environment.withWorkflowAllowed true),
            .authorize]
          spent ∧
        spent.spendCount = 1 ∧
        spent.proposal.proposalWork = spent.proposal.expectedWork := by
  let loosened := state.withEnvironment
    (state.environment.withWorkflowAllowed true)
  have gates : CurrentAuthorizationGates loosened :=
    ⟨observationUsable, basisPinned, rfl, standing⟩
  exact ⟨refused, .cons (.changeEnvironment state _)
      (.cons (.authorize loosened admissible gates unused) (.nil _)), rfl, workBound⟩

/-! ## Axiom receipt -/

#print axioms spend_implies_authorization_gates
#print axioms spend_implies_current_authorization_gates
#print axioms authorization_transition_mints_one_spend
#print axioms proposal_recorded_is_inert
#print axioms record_proposal_does_not_mint_spend
#print axioms admissibility_is_inert
#print axioms admissibility_does_not_mint_spend
#print axioms environment_change_does_not_mint_spend
#print axioms closed_standing_prevents_spend
#print axioms changed_evidence_basis_prevents_spend
#print axioms work_mismatch_prevents_spend
#print axioms work_mismatch_prevents_recording
#print axioms reachable_recorded_work_is_bound
#print axioms one_occurrence_cannot_mint_two_spends
#print axioms authorization_consumed_cannot_spend_again

end NightshiftGovernedAuthorization
