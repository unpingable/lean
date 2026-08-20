/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE
-/

/-
  A tiny deterministic partial-transition kernel.

  The kernel deliberately knows nothing about why a transition is legal.
  Domain adapters put their own criteria into `step`; this module supplies
  only execution, trace, and reachability structure.
-/

import Std

namespace TransitionKernel

universe uState uAct

/-- A deterministic transition system whose actions may be disabled. -/
structure PartialMachine (State : Type uState) (Act : Type uAct) where
  step : State → Act → Option State

namespace PartialMachine

variable {State : Type uState} {Act : Type uAct}

/-- Executing `act` at `state` produces exactly `next`. -/
def Step (M : PartialMachine State Act)
    (state : State) (act : Act) (next : State) : Prop :=
  M.step state act = some next

/-- An action is enabled exactly when the partial executor has a result. -/
def Enabled (M : PartialMachine State Act)
    (state : State) (act : Act) : Prop :=
  M.step state act ≠ none

/-- Execute a finite action trace, stopping at the first disabled action. -/
def run (M : PartialMachine State Act) :
    State → List Act → Option State
  | state, [] => some state
  | state, act :: rest =>
      match M.step state act with
      | none => none
      | some next => run M next rest

/-- A trace executes from `start` to the exact state `finish`. -/
def Runs (M : PartialMachine State Act)
    (start : State) (acts : List Act) (finish : State) : Prop :=
  M.run start acts = some finish

/-- Every action in the trace is legal from its prefix-produced state. -/
def LegalTrace (M : PartialMachine State Act)
    (start : State) (acts : List Act) : Prop :=
  ∃ finish, M.Runs start acts finish

/-- A state is reachable when some successfully executed trace reaches it. -/
def Reachable (M : PartialMachine State Act)
    (initial finish : State) : Prop :=
  ∃ acts, M.Runs initial acts finish

@[simp] theorem run_nil (M : PartialMachine State Act) (state : State) :
    M.run state [] = some state := rfl

theorem run_append (M : PartialMachine State Act)
    (start : State) (front back : List Act) :
    M.run start (front ++ back) =
      match M.run start front with
      | none => none
      | some middle => M.run middle back := by
  induction front generalizing start with
  | nil => rfl
  | cons act rest ih =>
      simp only [List.cons_append, run]
      cases hstep : M.step start act with
      | none => rfl
      | some next =>
          simpa using ih (start := next)

theorem step_deterministic (M : PartialMachine State Act)
    {state : State} {act : Act} {left right : State}
    (hleft : M.Step state act left)
    (hright : M.Step state act right) :
    left = right := by
  unfold Step at hleft hright
  rw [hleft] at hright
  exact Option.some.inj hright

theorem runs_deterministic (M : PartialMachine State Act)
    {start : State} {acts : List Act} {left right : State}
    (hleft : M.Runs start acts left)
    (hright : M.Runs start acts right) :
    left = right := by
  unfold Runs at hleft hright
  rw [hleft] at hright
  exact Option.some.inj hright

theorem empty_runs (M : PartialMachine State Act) (state : State) :
    M.Runs state [] state := rfl

theorem empty_trace_legal (M : PartialMachine State Act) (state : State) :
    M.LegalTrace state [] :=
  ⟨state, M.empty_runs state⟩

theorem enabled_iff_exists_step (M : PartialMachine State Act)
    (state : State) (act : Act) :
    M.Enabled state act ↔ ∃ next, M.Step state act next := by
  unfold Enabled Step
  cases hstep : M.step state act with
  | none =>
      constructor
      · intro enabled
        exact False.elim (enabled rfl)
      · rintro ⟨next, impossible⟩
        exact nomatch impossible
  | some next =>
      constructor
      · intro _
        exact ⟨next, rfl⟩
      · intro _ equality
        exact nomatch equality

theorem run_singleton (M : PartialMachine State Act)
    (state : State) (act : Act) :
    M.run state [act] = M.step state act := by
  unfold run
  cases M.step state act <;> rfl

theorem step_iff_runs_singleton (M : PartialMachine State Act)
    (state : State) (act : Act) (next : State) :
    M.Step state act next ↔ M.Runs state [act] next := by
  unfold Step Runs
  rw [run_singleton]

theorem runs_append_iff (M : PartialMachine State Act)
    {start finish : State} {front back : List Act} :
    M.Runs start (front ++ back) finish ↔
      ∃ middle,
        M.Runs start front middle ∧
        M.Runs middle back finish := by
  constructor
  · intro whole
    unfold Runs at whole ⊢
    rw [run_append] at whole
    cases hfront : M.run start front with
    | none =>
        rw [hfront] at whole
        exact nomatch whole
    | some middle =>
        rw [hfront] at whole
        exact ⟨middle, rfl, whole⟩
  · rintro ⟨middle, frontRuns, backRuns⟩
    unfold Runs at frontRuns backRuns ⊢
    rw [run_append, frontRuns]
    exact backRuns

/-- Legal append is exactly legal prefix execution followed by a legal suffix
from the prefix-produced state. This is both decomposition and composition. -/
theorem legalTrace_append_iff (M : PartialMachine State Act)
    {start : State} {front back : List Act} :
    M.LegalTrace start (front ++ back) ↔
      ∃ middle,
        M.Runs start front middle ∧
        M.LegalTrace middle back := by
  constructor
  · rintro ⟨finish, whole⟩
    obtain ⟨middle, frontRuns, backRuns⟩ :=
      (M.runs_append_iff).mp whole
    exact ⟨middle, frontRuns, finish, backRuns⟩
  · rintro ⟨middle, frontRuns, finish, backRuns⟩
    exact ⟨finish,
      (M.runs_append_iff).mpr ⟨middle, frontRuns, backRuns⟩⟩

theorem legal_prefix_of_append (M : PartialMachine State Act)
    {start : State} {front back : List Act}
    (whole : M.LegalTrace start (front ++ back)) :
    M.LegalTrace start front := by
  obtain ⟨middle, frontRuns, _⟩ :=
    (M.legalTrace_append_iff).mp whole
  exact ⟨middle, frontRuns⟩

theorem legalTrace_append (M : PartialMachine State Act)
    {start middle : State} {front back : List Act}
    (frontRuns : M.Runs start front middle)
    (backLegal : M.LegalTrace middle back) :
    M.LegalTrace start (front ++ back) :=
  (M.legalTrace_append_iff).mpr ⟨middle, frontRuns, backLegal⟩

theorem legalTrace_has_unique_result (M : PartialMachine State Act)
    {start : State} {acts : List Act}
    (legal : M.LegalTrace start acts) :
    ∃ finish,
      M.Runs start acts finish ∧
      ∀ other, M.Runs start acts other → other = finish := by
  obtain ⟨finish, runs⟩ := legal
  refine ⟨finish, runs, ?_⟩
  intro other otherRuns
  exact M.runs_deterministic otherRuns runs

theorem initial_reachable (M : PartialMachine State Act) (initial : State) :
    M.Reachable initial initial :=
  ⟨[], M.empty_runs initial⟩

theorem reachable_of_runs (M : PartialMachine State Act)
    {initial finish : State} {acts : List Act}
    (runs : M.Runs initial acts finish) :
    M.Reachable initial finish :=
  ⟨acts, runs⟩

theorem reachable_step (M : PartialMachine State Act)
    {initial state next : State} {act : Act}
    (reachable : M.Reachable initial state)
    (step : M.Step state act next) :
    M.Reachable initial next := by
  obtain ⟨history, historyRuns⟩ := reachable
  refine ⟨history ++ [act], ?_⟩
  apply (M.runs_append_iff).mpr
  exact ⟨state, historyRuns,
    (M.step_iff_runs_singleton state act next).mp step⟩

theorem reachable_enabled (M : PartialMachine State Act)
    {initial state : State} {act : Act}
    (reachable : M.Reachable initial state)
    (enabled : M.Enabled state act) :
    ∃ next,
      M.Step state act next ∧
      M.Reachable initial next := by
  obtain ⟨next, step⟩ := (M.enabled_iff_exists_step state act).mp enabled
  exact ⟨next, step, M.reachable_step reachable step⟩

end PartialMachine

end TransitionKernel
