/-
  LeanProofs.ViewSemantics.DynamicTraceAdapter -- observation views over
  already-authorized v9 dynamic traces.

  Custody-Class: UNRATIFIED-CANDIDATE

  This Gate C adapter deliberately keeps two inputs separate:

  * `AuthorizedRun` contains an `Admissibility.DynamicTrace.AuthorizedTrace`
    supplied by the v9 execution bridge; and
  * a `TraceView` only observes such a run.

  Re-observing a run through a finer or joint view returns the exact input run
  and trace.  No definition in this module constructs an `AuthorizedStep`, a
  `DynamicStep`, or an `AuthorizedTrace`.  The separation receipts at the end
  reuse v9's revoked-basis and missing-authority walls to show that even full
  state visibility does not authorize a blocked hop.

  This is an adapter over authorized evidence, not process semantics, a
  scheduler, a source of transition authority, or a promotion of the v9 ANNEX.
-/

import LeanProofs.ViewSemantics.Core
import LeanProofs.Admissibility.DynamicTrace

namespace LeanProofs.ViewSemantics.DynamicTraceAdapter

open Admissibility.Authority
open Admissibility.StateTransition
open Admissibility.Execution
open Admissibility.DynamicTrace

universe u v w

/-! ## Authorized runs are the world type consumed by trace views -/

/--
  A fixed-start run packages an endpoint together with the v9
  `AuthorizedTrace` evidence that reaches it.  The evidence is an input to this
  adapter: there is no constructor here from endpoints or observations alone.
-/
structure AuthorizedRun
    (env : ExecutionEnv)
    (actor : Actor)
    (start : GovState) where
  finish : GovState
  trace : AuthorizedTrace env actor start finish

/-- A view whose worlds are already-authorized runs. -/
abbrev TraceView
    (env : ExecutionEnv)
    (actor : Actor)
    (start : GovState)
    (Observation : Type u) :=
  View (AuthorizedRun env actor start) Observation

/-- Observe an authorized run through its endpoint. -/
def endpointView
    {env : ExecutionEnv}
    {actor : Actor}
    {start : GovState}
    {Observation : Type u}
    (stateView : View GovState Observation) :
    TraceView env actor start Observation :=
  fun run => stateView run.finish

/--
  The v9 static-step projection is itself a trace view.  This is a substantive
  adapter point: the returned list is computed from supplied
  `AuthorizedTrace` evidence, not from an arbitrary proposed path.
-/
def stepSequenceView
    {env : ExecutionEnv}
    {actor : Actor}
    {start : GovState} :
    TraceView env actor start (List Step) :=
  fun run => traceSteps run.trace

@[simp] theorem stepSequenceView_eq_traceSteps
    {env : ExecutionEnv}
    {actor : Actor}
    {start : GovState}
    (run : AuthorizedRun env actor start) :
    stepSequenceView run = traceSteps run.trace :=
  rfl

/-- Refinement between state views lifts pointwise to their endpoint views. -/
theorem endpointView_refines
    {env : ExecutionEnv}
    {actor : Actor}
    {start : GovState}
    {FineObservation : Type u}
    {CoarseObservation : Type v}
    {fine : View GovState FineObservation}
    {coarse : View GovState CoarseObservation}
    (hRefines : Refines fine coarse) :
    Refines
      (endpointView (env := env) (actor := actor) (start := start) fine)
      (endpointView (env := env) (actor := actor) (start := start) coarse) := by
  intro left right hFine
  exact hRefines left.finish right.finish hFine

/-! ## Observation wrappers that reuse, rather than manufacture, traces -/

/--
  An observation paired with the already-authorized run that produced it.
  `observation_eq` prevents the wrapper from attaching an invented observation
  to the run.
-/
structure ViewedAuthorizedRun
    {env : ExecutionEnv}
    {actor : Actor}
    {start : GovState}
    {Observation : Type u}
    (view : TraceView env actor start Observation) where
  run : AuthorizedRun env actor start
  observation : Observation
  observation_eq : observation = view run

/-- Consume an existing authorized run and expose its observation. -/
def observe
    {env : ExecutionEnv}
    {actor : Actor}
    {start : GovState}
    {Observation : Type u}
    (view : TraceView env actor start Observation)
    (run : AuthorizedRun env actor start) :
    ViewedAuthorizedRun view :=
  { run := run
    observation := view run
    observation_eq := rfl }

@[simp] theorem observe_run
    {env : ExecutionEnv}
    {actor : Actor}
    {start : GovState}
    {Observation : Type u}
    (view : TraceView env actor start Observation)
    (run : AuthorizedRun env actor start) :
    (observe view run).run = run :=
  rfl

/--
  Change the observation interface while retaining the exact supplied run.
  This operation needs a `ViewedAuthorizedRun`; a view alone is insufficient.
-/
def reobserve
    {env : ExecutionEnv}
    {actor : Actor}
    {start : GovState}
    {OldObservation : Type u}
    {NewObservation : Type v}
    {oldView : TraceView env actor start OldObservation}
    (newView : TraceView env actor start NewObservation)
    (seen : ViewedAuthorizedRun oldView) :
    ViewedAuthorizedRun newView :=
  observe newView seen.run

/--
  Re-observe through a certified finer view.  The refinement proof changes the
  epistemic comparison only; the output still contains `seen.run` verbatim.
-/
def refineObservation
    {env : ExecutionEnv}
    {actor : Actor}
    {start : GovState}
    {FineObservation : Type u}
    {CoarseObservation : Type v}
    {fine : TraceView env actor start FineObservation}
    {coarse : TraceView env actor start CoarseObservation}
    (_hRefines : Refines fine coarse)
    (seen : ViewedAuthorizedRun coarse) :
    ViewedAuthorizedRun fine :=
  reobserve fine seen

@[simp] theorem refineObservation_reuses_run
    {env : ExecutionEnv}
    {actor : Actor}
    {start : GovState}
    {FineObservation : Type u}
    {CoarseObservation : Type v}
    {fine : TraceView env actor start FineObservation}
    {coarse : TraceView env actor start CoarseObservation}
    (hRefines : Refines fine coarse)
    (seen : ViewedAuthorizedRun coarse) :
    (refineObservation hRefines seen).run = seen.run :=
  rfl

@[simp] theorem refineObservation_reuses_trace
    {env : ExecutionEnv}
    {actor : Actor}
    {start : GovState}
    {FineObservation : Type u}
    {CoarseObservation : Type v}
    {fine : TraceView env actor start FineObservation}
    {coarse : TraceView env actor start CoarseObservation}
    (hRefines : Refines fine coarse)
    (seen : ViewedAuthorizedRun coarse) :
    (refineObservation hRefines seen).run.trace = seen.run.trace :=
  rfl

@[simp] theorem refineObservation_preserves_step_sequence
    {env : ExecutionEnv}
    {actor : Actor}
    {start : GovState}
    {FineObservation : Type u}
    {CoarseObservation : Type v}
    {fine : TraceView env actor start FineObservation}
    {coarse : TraceView env actor start CoarseObservation}
    (hRefines : Refines fine coarse)
    (seen : ViewedAuthorizedRun coarse) :
    stepSequenceView (refineObservation hRefines seen).run =
      stepSequenceView seen.run :=
  rfl

/--
  Expose a joint observation of an existing run.  As with refinement, the run
  is an input and is returned unchanged.
-/
def joinObservation
    {env : ExecutionEnv}
    {actor : Actor}
    {start : GovState}
    {Observation₁ : Type u}
    {Observation₂ : Type v}
    (first : TraceView env actor start Observation₁)
    (second : TraceView env actor start Observation₂)
    (run : AuthorizedRun env actor start) :
    ViewedAuthorizedRun (compose first second) :=
  observe (compose first second) run

@[simp] theorem joinObservation_reuses_run
    {env : ExecutionEnv}
    {actor : Actor}
    {start : GovState}
    {Observation₁ : Type u}
    {Observation₂ : Type v}
    (first : TraceView env actor start Observation₁)
    (second : TraceView env actor start Observation₂)
    (run : AuthorizedRun env actor start) :
    (joinObservation first second run).run = run :=
  rfl

@[simp] theorem joinObservation_reuses_trace
    {env : ExecutionEnv}
    {actor : Actor}
    {start : GovState}
    {Observation₁ : Type u}
    {Observation₂ : Type v}
    (first : TraceView env actor start Observation₁)
    (second : TraceView env actor start Observation₂)
    (run : AuthorizedRun env actor start) :
    (joinObservation first second run).run.trace = run.trace :=
  rfl

@[simp] theorem joinObservation_preserves_step_sequence
    {env : ExecutionEnv}
    {actor : Actor}
    {start : GovState}
    {Observation₁ : Type u}
    {Observation₂ : Type v}
    (first : TraceView env actor start Observation₁)
    (second : TraceView env actor start Observation₂)
    (run : AuthorizedRun env actor start) :
    stepSequenceView (joinObservation first second run).run =
      stepSequenceView run :=
  rfl

/-- Joining trace views changes indistinguishability by intersecting the two
component equivalence classes, exactly as in the shared core. -/
theorem joinTraceView_indistinguishable_iff
    {env : ExecutionEnv}
    {actor : Actor}
    {start : GovState}
    {Observation₁ : Type u}
    {Observation₂ : Type v}
    (first : TraceView env actor start Observation₁)
    (second : TraceView env actor start Observation₂)
    (left right : AuthorizedRun env actor start) :
    Indistinguishable (compose first second) left right ↔
      Indistinguishable first left right ∧
      Indistinguishable second left right :=
  compose_indistinguishable_iff first second left right

/-- The semantic effect of refinement remains the core implication between
observation equalities; it does not mention or return transition evidence. -/
theorem refined_trace_indistinguishability_implies_coarse
    {env : ExecutionEnv}
    {actor : Actor}
    {start : GovState}
    {FineObservation : Type u}
    {CoarseObservation : Type v}
    {fine : TraceView env actor start FineObservation}
    {coarse : TraceView env actor start CoarseObservation}
    (hRefines : Refines fine coarse)
    {left right : AuthorizedRun env actor start}
    (hFine : Indistinguishable fine left right) :
    Indistinguishable coarse left right :=
  hRefines left right hFine

/-! ## Separation fixtures: visibility never fills an authority gap -/

/-- A view that exposes no state distinction. -/
def blindStateView : View GovState Unit :=
  fun _ => ()

/-- The maximally direct state view. -/
def fullStateView : View GovState GovState :=
  fun state => state

/-- Full state visibility refines the blind view. -/
theorem fullStateView_refines_blindStateView :
    Refines fullStateView blindStateView := by
  intro _ _ _
  rfl

/--
  Explicit revoked-basis separation fixture.  Observation improves from no
  state distinctions to the full state, while v9's revoked-basis wall still
  forbids the proposed dynamic hop.  The conclusion is a conjunction to keep
  the epistemic and authorization verdicts independent.
-/
theorem full_visibility_does_not_override_revoked_basis
    {env : ExecutionEnv}
    {state finish : GovState}
    {actor : Actor}
    {step : Step}
    (hRevoked :
      env.derivation.basis.basisRevoked
        state
        (env.claimForStep state actor step)) :
    Refines fullStateView blindStateView ∧
      ¬ ∃ dyn : DynamicStep env actor state finish,
          dyn.authorized.step = step :=
  ⟨fullStateView_refines_blindStateView,
    revoked_basis_blocks_dynamic_step hRevoked⟩

/--
  The same separation at the two-input execution wall: even full visibility
  plus mutation-side standing cannot replace the missing claim-side authority
  needed by a `DynamicStep`.
-/
theorem full_visibility_does_not_supply_missing_authority
    {env : ExecutionEnv}
    {state finish : GovState}
    {actor : Actor}
    {step : Step}
    (hAllowed : StepAllowed state actor step)
    (hNotAuthorized :
      stepAuthorityVerdict env state actor step ≠
        AuthorityVerdict.authorized) :
    Refines fullStateView blindStateView ∧
      ¬ ∃ dyn : DynamicStep env actor state finish,
          dyn.authorized.step = step :=
  ⟨fullStateView_refines_blindStateView,
    step_allowed_without_authority_blocks_dynamic_step
      hAllowed hNotAuthorized⟩

/-! ## Candidate axiom-footprint receipts -/

#print axioms endpointView_refines
#print axioms refineObservation_reuses_trace
#print axioms refineObservation_preserves_step_sequence
#print axioms joinObservation_reuses_trace
#print axioms joinObservation_preserves_step_sequence
#print axioms joinTraceView_indistinguishable_iff
#print axioms fullStateView_refines_blindStateView
#print axioms full_visibility_does_not_override_revoked_basis
#print axioms full_visibility_does_not_supply_missing_authority

end LeanProofs.ViewSemantics.DynamicTraceAdapter
