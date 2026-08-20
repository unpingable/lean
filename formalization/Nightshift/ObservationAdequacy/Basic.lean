/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE
-/

/-
  Relational transition plumbing for observation-adequacy tests.

  `RelSystem` is intentionally semantically neutral. Its step relation may be
  used for execution, protocol admission, or another domain-selected notion,
  but the generic library does not identify those meanings.
-/

import Std

namespace ObservationAdequacy

universe uState uAct

/-- A transition system in which one state/action pair may have several
successors. No executability, finiteness, or determinism is assumed. -/
structure RelSystem (State : Type uState) (Act : Type uAct) where
  step : State → Act → State → Prop

namespace RelSystem

variable {State : Type uState} {Act : Type uAct}

def Step (S : RelSystem State Act)
    (state : State) (act : Act) (next : State) : Prop :=
  S.step state act next

/-- Existential/may enabledness: the action has at least one successor. -/
def Enabled (S : RelSystem State Act)
    (state : State) (act : Act) : Prop :=
  ∃ next, S.Step state act next

/-- An exact realized state path for an action list. -/
inductive Runs (S : RelSystem State Act) :
    State → List Act → State → Prop where
  | nil (state : State) : S.Runs state [] state
  | cons {state next finish : State} {act : Act} {rest : List Act} :
      S.Step state act next →
      S.Runs next rest finish →
      S.Runs state (act :: rest) finish

/-- Existential/may trace legality. Under nondeterminism this does not mean
that every possible outcome can execute the action list. -/
def LegalTrace (S : RelSystem State Act)
    (start : State) (acts : List Act) : Prop :=
  ∃ finish, S.Runs start acts finish

def Reachable (S : RelSystem State Act)
    (initial finish : State) : Prop :=
  ∃ acts, S.Runs initial acts finish

theorem empty_runs (S : RelSystem State Act) (state : State) :
    S.Runs state [] state :=
  .nil state

theorem empty_trace_legal (S : RelSystem State Act) (state : State) :
    S.LegalTrace state [] :=
  ⟨state, .nil state⟩

theorem initial_reachable (S : RelSystem State Act) (initial : State) :
    S.Reachable initial initial :=
  ⟨[], .nil initial⟩

theorem enabled_iff_exists_step (S : RelSystem State Act)
    (state : State) (act : Act) :
    S.Enabled state act ↔ ∃ next, S.Step state act next :=
  Iff.rfl

theorem runs_singleton_iff_step (S : RelSystem State Act)
    {state next : State} {act : Act} :
    S.Runs state [act] next ↔ S.Step state act next := by
  constructor
  · intro runs
    cases runs with
    | cons step tail =>
        cases tail
        exact step
  · intro step
    exact .cons step (.nil next)

theorem legalTrace_singleton_iff_enabled (S : RelSystem State Act)
    (state : State) (act : Act) :
    S.LegalTrace state [act] ↔ S.Enabled state act := by
  constructor
  · rintro ⟨next, runs⟩
    exact ⟨next, (S.runs_singleton_iff_step).mp runs⟩
  · rintro ⟨next, step⟩
    exact ⟨next, (S.runs_singleton_iff_step).mpr step⟩

theorem runs_append (S : RelSystem State Act)
    {start middle finish : State} {front back : List Act}
    (frontRuns : S.Runs start front middle)
    (backRuns : S.Runs middle back finish) :
    S.Runs start (front ++ back) finish := by
  induction frontRuns with
  | nil => exact backRuns
  | cons step _ inductionHypothesis =>
      exact .cons step (inductionHypothesis backRuns)

theorem runs_append_decompose (S : RelSystem State Act)
    {start finish : State} {front back : List Act}
    (whole : S.Runs start (front ++ back) finish) :
    ∃ middle,
      S.Runs start front middle ∧
      S.Runs middle back finish := by
  induction front generalizing start with
  | nil =>
      exact ⟨start, .nil start, whole⟩
  | cons act rest inductionHypothesis =>
      cases whole with
      | cons firstStep tailRuns =>
          obtain ⟨middle, frontRuns, backRuns⟩ :=
            inductionHypothesis tailRuns
          exact ⟨middle, .cons firstStep frontRuns, backRuns⟩

theorem legalTrace_append_iff (S : RelSystem State Act)
    {start : State} {front back : List Act} :
    S.LegalTrace start (front ++ back) ↔
      ∃ middle,
        S.Runs start front middle ∧
        S.LegalTrace middle back := by
  constructor
  · rintro ⟨finish, whole⟩
    obtain ⟨middle, frontRuns, backRuns⟩ :=
      S.runs_append_decompose whole
    exact ⟨middle, frontRuns, finish, backRuns⟩
  · rintro ⟨middle, frontRuns, finish, backRuns⟩
    exact ⟨finish, S.runs_append frontRuns backRuns⟩

theorem legalTrace_append (S : RelSystem State Act)
    {start middle : State} {front back : List Act}
    (frontRuns : S.Runs start front middle)
    (backLegal : S.LegalTrace middle back) :
    S.LegalTrace start (front ++ back) :=
  (S.legalTrace_append_iff).mpr ⟨middle, frontRuns, backLegal⟩

theorem legal_prefix_of_append (S : RelSystem State Act)
    {start : State} {front back : List Act}
    (whole : S.LegalTrace start (front ++ back)) :
    S.LegalTrace start front := by
  obtain ⟨middle, frontRuns, _⟩ :=
    (S.legalTrace_append_iff).mp whole
  exact ⟨middle, frontRuns⟩

theorem reachable_of_runs (S : RelSystem State Act)
    {initial finish : State} {history : List Act}
    (runs : S.Runs initial history finish) :
    S.Reachable initial finish :=
  ⟨history, runs⟩

theorem reachable_step (S : RelSystem State Act)
    {initial state next : State} {act : Act}
    (reachable : S.Reachable initial state)
    (step : S.Step state act next) :
    S.Reachable initial next := by
  obtain ⟨history, historyRuns⟩ := reachable
  exact ⟨history ++ [act],
    S.runs_append historyRuns (.cons step (.nil next))⟩

theorem reachable_enabled (S : RelSystem State Act)
    {initial state : State} {act : Act}
    (reachable : S.Reachable initial state)
    (enabled : S.Enabled state act) :
    ∃ next,
      S.Step state act next ∧
      S.Reachable initial next := by
  obtain ⟨next, step⟩ := enabled
  exact ⟨next, step, S.reachable_step reachable step⟩

end RelSystem

end ObservationAdequacy
