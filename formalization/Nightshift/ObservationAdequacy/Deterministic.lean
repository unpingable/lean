/-
  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: PUBLIC-EVIDENCE
-/

/-
  Compatibility with the existing deterministic experimental kernel.

  `PartialMachine` is retained unchanged. Its graph is a `RelSystem`; the
  equivalence theorems below show that no deterministic traces are gained or
  lost by using the relational observation toolkit.
-/

import ObservationAdequacy.Basic
import TransitionKernel.Basic

namespace ObservationAdequacy

universe uState uAct

variable {State : Type uState} {Act : Type uAct}

def ofPartial (M : TransitionKernel.PartialMachine State Act) :
    RelSystem State Act :=
  ⟨M.Step⟩

theorem ofPartial_step_iff
    (M : TransitionKernel.PartialMachine State Act)
    (state : State) (act : Act) (next : State) :
    (ofPartial M).Step state act next ↔ M.Step state act next :=
  Iff.rfl

theorem ofPartial_enabled_iff
    (M : TransitionKernel.PartialMachine State Act)
    (state : State) (act : Act) :
    (ofPartial M).Enabled state act ↔ M.Enabled state act := by
  constructor
  · rintro ⟨next, step⟩
    exact (M.enabled_iff_exists_step state act).mpr ⟨next, step⟩
  · intro enabled
    obtain ⟨next, step⟩ :=
      (M.enabled_iff_exists_step state act).mp enabled
    exact ⟨next, step⟩

theorem ofPartial_runs_iff
    (M : TransitionKernel.PartialMachine State Act)
    {start finish : State} {history : List Act} :
    (ofPartial M).Runs start history finish ↔
      M.Runs start history finish := by
  constructor
  · intro relationalRuns
    induction relationalRuns with
    | nil => exact M.empty_runs _
    | cons step _ inductionHypothesis =>
        unfold TransitionKernel.PartialMachine.Runs
        unfold TransitionKernel.PartialMachine.Step at step
        simp only [TransitionKernel.PartialMachine.run]
        rw [step]
        exact inductionHypothesis
  · intro deterministicRuns
    induction history generalizing start finish with
    | nil =>
        have same : start = finish :=
          Option.some.inj deterministicRuns
        subst finish
        exact .nil start
    | cons act rest inductionHypothesis =>
        unfold TransitionKernel.PartialMachine.Runs at deterministicRuns
        simp only [TransitionKernel.PartialMachine.run] at deterministicRuns
        cases hstep : M.step start act with
        | none =>
            rw [hstep] at deterministicRuns
            exact nomatch deterministicRuns
        | some next =>
            rw [hstep] at deterministicRuns
            exact .cons hstep
              (inductionHypothesis deterministicRuns)

theorem ofPartial_legalTrace_iff
    (M : TransitionKernel.PartialMachine State Act)
    (start : State) (history : List Act) :
    (ofPartial M).LegalTrace start history ↔
      M.LegalTrace start history := by
  constructor
  · rintro ⟨finish, runs⟩
    exact ⟨finish, (ofPartial_runs_iff M).mp runs⟩
  · rintro ⟨finish, runs⟩
    exact ⟨finish, (ofPartial_runs_iff M).mpr runs⟩

theorem ofPartial_reachable_iff
    (M : TransitionKernel.PartialMachine State Act)
    (initial state : State) :
    (ofPartial M).Reachable initial state ↔
      M.Reachable initial state := by
  constructor
  · rintro ⟨history, runs⟩
    exact ⟨history, (ofPartial_runs_iff M).mp runs⟩
  · rintro ⟨history, runs⟩
    exact ⟨history, (ofPartial_runs_iff M).mpr runs⟩

/-- The uniqueness laws are compatibility facts of the deterministic source;
they are not laws of arbitrary `RelSystem`s. -/
theorem ofPartial_successor_unique
    (M : TransitionKernel.PartialMachine State Act)
    {state left right : State} {act : Act}
    (leftStep : (ofPartial M).Step state act left)
    (rightStep : (ofPartial M).Step state act right) :
    left = right :=
  M.step_deterministic leftStep rightStep

end ObservationAdequacy
