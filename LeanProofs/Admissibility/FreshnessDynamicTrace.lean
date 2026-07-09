/-
  Custody-Class: ANNEX

  Admissibility.FreshnessDynamicTrace -- freshness-gated dynamic traces.

  This module connects the ANNEX dynamic trace wrapper to the public
  metric-time freshness kernel. A dynamic step still carries the same
  underlying `DynamicStep`; the additional obligation is that the observation
  used at the current discharge time is fresh.

  ANNEX, NOT PUBLIC SURFACE:
    * not imported by `AdmissibilityKernels.lean`;
    * not part of the 1.0 compatibility claim;
    * not an actor-indexed trace calculus;
    * not NQ-specific code. The method tag is an abstract consumer-supplied
      type parameter.
-/

import LeanProofs.Admissibility.DynamicTrace
import LeanProofs.Admissibility.Freshness

namespace Admissibility.FreshnessDynamicTrace

open Admissibility.Authority
open Admissibility.StateTransition
open Admissibility.Execution
open Admissibility.DynamicTrace
open Admissibility.Freshness

/-! ## Fresh observations -/

/--
  Minimal NQ-shaped observation payload. `Method` is an abstract consumer tag;
  the freshness gate depends only on the metric-time fields.
-/
structure Observation (Method : Type) where
  method : Method
  issued : Time
  expires : Time
  skew : Time
  maxDiv : Time

/-- An observation is fresh at current use time exactly when the public
    `Freshness.Fresh` predicate holds for its timestamp fields. -/
def ObservationFreshAt {Method : Type}
    (now : Time)
    (obs : Observation Method) : Prop :=
  Fresh now obs.issued obs.expires obs.skew obs.maxDiv

/-! ## Fresh-gated dynamic one-step wrapper -/

/--
  A freshness-gated dynamic step is an ordinary authorized dynamic step plus
  the observation used to discharge the current obligation and a proof that
  this observation is fresh at `now`.
-/
structure FreshDynamicStep
    (now : Time)
    (Method : Type)
    (env : ExecutionEnv)
    (actor : Actor)
    (start finish : GovState) where
  dynamic : DynamicStep env actor start finish
  observation : Observation Method
  fresh : ObservationFreshAt now observation

/-- Fresh dynamic execution still requires claim-side authorization. -/
theorem fresh_dynamic_step_requires_authority
    {now : Time}
    {Method : Type}
    {env : ExecutionEnv}
    {actor : Actor}
    {start finish : GovState}
    (step : FreshDynamicStep now Method env actor start finish) :
    stepAuthorityVerdict env start actor step.dynamic.authorized.step =
      AuthorityVerdict.authorized :=
  dynamic_step_requires_authority step.dynamic

/-- Fresh dynamic execution exposes the freshness proof it consumed. -/
theorem fresh_dynamic_step_requires_fresh_observation
    {now : Time}
    {Method : Type}
    {env : ExecutionEnv}
    {actor : Actor}
    {start finish : GovState}
    (step : FreshDynamicStep now Method env actor start finish) :
    ObservationFreshAt now step.observation :=
  step.fresh

/-! ## Freshness refusal wrappers -/

/--
  A stale observation cannot discharge a current fresh dynamic obligation,
  even if some ordinary dynamic step exists.
-/
theorem stale_observation_cannot_discharge_current_obligation
    {now : Time}
    {Method : Type}
    {env : ExecutionEnv}
    {actor : Actor}
    {start finish : GovState}
    {obs : Observation Method}
    (hstale : ¬ ObservationFreshAt now obs) :
    ¬ ∃ step : FreshDynamicStep now Method env actor start finish,
        step.observation = obs := by
  intro h
  rcases h with ⟨step, hobs⟩
  exact hstale (by
    rw [← hobs]
    exact step.fresh)

/-- Expired observations are not fresh at the current use time. -/
theorem expired_observation_not_fresh
    {now : Time}
    {Method : Type}
    {obs : Observation Method}
    (h : ¬ (now ≤ obs.expires + obs.skew)) :
    ¬ ObservationFreshAt now obs :=
  expired_not_fresh h

/-- Not-yet-valid observations are not fresh at the current use time. -/
theorem not_yet_valid_observation_not_fresh
    {now : Time}
    {Method : Type}
    {obs : Observation Method}
    (h : ¬ ((obs.issued - obs.skew) ≤ now)) :
    ¬ ObservationFreshAt now obs :=
  not_yet_valid_not_fresh h

/-- Temporally incoherent observations are not fresh at the current use time. -/
theorem incoherent_observation_not_fresh
    {now : Time}
    {Method : Type}
    {obs : Observation Method}
    (h : obs.expires ≤ obs.issued) :
    ¬ ObservationFreshAt now obs :=
  incoherent_not_fresh h

/-- Observations whose issue time does not precede expiry are not fresh. -/
theorem not_precedes_observation_not_fresh
    {now : Time}
    {Method : Type}
    {obs : Observation Method}
    (h : ¬ (obs.issued ≤ obs.expires)) :
    ¬ ObservationFreshAt now obs :=
  not_precedes_not_fresh h

/-- Observations with excessive verifier/issuer divergence are not fresh. -/
theorem divergence_excessive_observation_not_fresh
    {now : Time}
    {Method : Type}
    {obs : Observation Method}
    (h : ¬ (Time.absSub now obs.issued ≤ obs.maxDiv)) :
    ¬ ObservationFreshAt now obs :=
  divergence_excessive_not_fresh h

/-- An expired observation cannot discharge a current fresh dynamic step. -/
theorem expired_observation_cannot_discharge_current_obligation
    {now : Time}
    {Method : Type}
    {env : ExecutionEnv}
    {actor : Actor}
    {start finish : GovState}
    {obs : Observation Method}
    (h : ¬ (now ≤ obs.expires + obs.skew)) :
    ¬ ∃ step : FreshDynamicStep now Method env actor start finish,
        step.observation = obs :=
  stale_observation_cannot_discharge_current_obligation
    (expired_observation_not_fresh h)

/-- A not-yet-valid observation cannot discharge a current fresh dynamic step. -/
theorem not_yet_valid_observation_cannot_discharge_current_obligation
    {now : Time}
    {Method : Type}
    {env : ExecutionEnv}
    {actor : Actor}
    {start finish : GovState}
    {obs : Observation Method}
    (h : ¬ ((obs.issued - obs.skew) ≤ now)) :
    ¬ ∃ step : FreshDynamicStep now Method env actor start finish,
        step.observation = obs :=
  stale_observation_cannot_discharge_current_obligation
    (not_yet_valid_observation_not_fresh h)

/-- An incoherent observation cannot discharge a current fresh dynamic step. -/
theorem incoherent_observation_cannot_discharge_current_obligation
    {now : Time}
    {Method : Type}
    {env : ExecutionEnv}
    {actor : Actor}
    {start finish : GovState}
    {obs : Observation Method}
    (h : obs.expires ≤ obs.issued) :
    ¬ ∃ step : FreshDynamicStep now Method env actor start finish,
        step.observation = obs :=
  stale_observation_cannot_discharge_current_obligation
    (incoherent_observation_not_fresh h)

/--
  An observation whose issue time does not precede expiry cannot discharge a
  current fresh dynamic step.
-/
theorem not_precedes_observation_cannot_discharge_current_obligation
    {now : Time}
    {Method : Type}
    {env : ExecutionEnv}
    {actor : Actor}
    {start finish : GovState}
    {obs : Observation Method}
    (h : ¬ (obs.issued ≤ obs.expires)) :
    ¬ ∃ step : FreshDynamicStep now Method env actor start finish,
        step.observation = obs :=
  stale_observation_cannot_discharge_current_obligation
    (not_precedes_observation_not_fresh h)

/--
  An observation with excessive verifier/issuer divergence cannot discharge a
  current fresh dynamic step.
-/
theorem divergence_excessive_observation_cannot_discharge_current_obligation
    {now : Time}
    {Method : Type}
    {env : ExecutionEnv}
    {actor : Actor}
    {start finish : GovState}
    {obs : Observation Method}
    (h : ¬ (Time.absSub now obs.issued ≤ obs.maxDiv)) :
    ¬ ∃ step : FreshDynamicStep now Method env actor start finish,
        step.observation = obs :=
  stale_observation_cannot_discharge_current_obligation
    (divergence_excessive_observation_not_fresh h)

/-! ## State-threaded fresh traces -/

/--
  A state-threaded dynamic trace whose every hop carries a fresh observation
  at the same current use time.
-/
inductive FreshAuthorizedTrace
    (now : Time)
    (Method : Type)
    (env : ExecutionEnv)
    (actor : Actor) :
    GovState → GovState → Type where
  | nil (state : GovState) :
      FreshAuthorizedTrace now Method env actor state state
  | cons
      {start mid finish : GovState}
      (step : FreshDynamicStep now Method env actor start mid)
      (rest : FreshAuthorizedTrace now Method env actor mid finish) :
      FreshAuthorizedTrace now Method env actor start finish

/-- Forget the freshness observations and recover the ordinary dynamic trace. -/
def FreshAuthorizedTrace.toAuthorizedTrace
    {now : Time}
    {Method : Type}
    {env : ExecutionEnv}
    {actor : Actor} :
    ∀ {start finish : GovState},
      FreshAuthorizedTrace now Method env actor start finish →
        AuthorizedTrace env actor start finish
  | _, _, FreshAuthorizedTrace.nil state =>
      AuthorizedTrace.nil state
  | _, _, FreshAuthorizedTrace.cons step rest =>
      AuthorizedTrace.cons step.dynamic
        (FreshAuthorizedTrace.toAuthorizedTrace rest)


/-! ## Schedule-indexed fresh traces -/

/--
  Schedule-indexed fresh traces record the exact actor sequence in the type.
  Each hop carries the fresh observation required for that actor's transition.
-/
inductive FreshAuthorizedTraceSchedule
    (now : Time)
    (Method : Type)
    (env : ExecutionEnv) :
    List Actor → GovState → GovState → Type where
  | nil (state : GovState) :
      FreshAuthorizedTraceSchedule now Method env [] state state
  | cons
      {actor : Actor}
      {actors : List Actor}
      {start mid finish : GovState}
      (step : FreshDynamicStep now Method env actor start mid)
      (rest : FreshAuthorizedTraceSchedule now Method env actors mid finish) :
      FreshAuthorizedTraceSchedule now Method env (actor :: actors) start finish

/-- View a fixed-actor fresh trace as a trace whose schedule repeats that actor. -/
def FreshAuthorizedTrace.toSchedule
    {now : Time}
    {Method : Type}
    {env : ExecutionEnv}
    {actor : Actor} :
    ∀ {start finish : GovState},
      (trace : FreshAuthorizedTrace now Method env actor start finish) →
        FreshAuthorizedTraceSchedule now Method env
          (List.replicate
            (traceSteps (FreshAuthorizedTrace.toAuthorizedTrace trace)).length
            actor) start finish
  | _, _, FreshAuthorizedTrace.nil state =>
      FreshAuthorizedTraceSchedule.nil state
  | _, _, FreshAuthorizedTrace.cons step rest =>
      FreshAuthorizedTraceSchedule.cons step
        (FreshAuthorizedTrace.toSchedule rest)

/-- Forget freshness while preserving the exact schedule index. -/
def FreshAuthorizedTraceSchedule.toAuthorizedTraceSchedule
    {now : Time}
    {Method : Type}
    {env : ExecutionEnv} :
    ∀ {actors : List Actor} {start finish : GovState},
      FreshAuthorizedTraceSchedule now Method env actors start finish →
        AuthorizedTraceSchedule env actors start finish
  | _, _, _, FreshAuthorizedTraceSchedule.nil state =>
      AuthorizedTraceSchedule.nil state
  | _, _, _, FreshAuthorizedTraceSchedule.cons step rest =>
      AuthorizedTraceSchedule.cons step.dynamic
        (FreshAuthorizedTraceSchedule.toAuthorizedTraceSchedule rest)

/-- Scheduling a fixed fresh trace commutes with forgetting freshness. -/
@[simp] theorem fresh_toSchedule_toAuthorizedTraceSchedule
    {now : Time}
    {Method : Type}
    {env : ExecutionEnv}
    {actor : Actor}
    {start finish : GovState}
    (trace : FreshAuthorizedTrace now Method env actor start finish) :
    FreshAuthorizedTraceSchedule.toAuthorizedTraceSchedule
        (FreshAuthorizedTrace.toSchedule trace) =
      AuthorizedTrace.toSchedule
        (FreshAuthorizedTrace.toAuthorizedTrace trace) := by
  induction trace with
  | nil _ =>
      rfl
  | cons _ _ ih =>
      simp [FreshAuthorizedTrace.toSchedule,
        FreshAuthorizedTraceSchedule.toAuthorizedTraceSchedule,
        FreshAuthorizedTrace.toAuthorizedTrace, AuthorizedTrace.toSchedule, ih]


/-! ## Actor-indexed fresh traces -/

/--
  Actor-indexed fresh traces record that each hop independently supplied a
  fresh observation for the actor that performed that hop.
-/
inductive FreshAuthorizedTraceAnyActor
    (now : Time)
    (Method : Type)
    (env : ExecutionEnv) :
    GovState → GovState → Type where
  | nil (state : GovState) :
      FreshAuthorizedTraceAnyActor now Method env state state
  | cons
      {actor : Actor}
      {start mid finish : GovState}
      (step : FreshDynamicStep now Method env actor start mid)
      (rest : FreshAuthorizedTraceAnyActor now Method env mid finish) :
      FreshAuthorizedTraceAnyActor now Method env start finish

/-- Forget the freshness observations and recover the AnyActor dynamic trace. -/
def FreshAuthorizedTraceAnyActor.toAuthorizedTraceAnyActor
    {now : Time}
    {Method : Type}
    {env : ExecutionEnv} :
    ∀ {start finish : GovState},
      FreshAuthorizedTraceAnyActor now Method env start finish →
        AuthorizedTraceAnyActor env start finish
  | _, _, FreshAuthorizedTraceAnyActor.nil state =>
      AuthorizedTraceAnyActor.nil state
  | _, _, FreshAuthorizedTraceAnyActor.cons step rest =>
      AuthorizedTraceAnyActor.cons step.dynamic
        (FreshAuthorizedTraceAnyActor.toAuthorizedTraceAnyActor rest)

/-- Forget the fixed actor and view a fresh trace as locally actor-indexed. -/
def FreshAuthorizedTrace.toAnyActor
    {now : Time}
    {Method : Type}
    {env : ExecutionEnv}
    {actor : Actor} :
    ∀ {start finish : GovState},
      FreshAuthorizedTrace now Method env actor start finish →
        FreshAuthorizedTraceAnyActor now Method env start finish
  | _, _, FreshAuthorizedTrace.nil state =>
      FreshAuthorizedTraceAnyActor.nil state
  | _, _, FreshAuthorizedTrace.cons step rest =>
      FreshAuthorizedTraceAnyActor.cons step
        (FreshAuthorizedTrace.toAnyActor rest)

/-- Forget the schedule index and view a fresh trace as locally actor-indexed. -/
def FreshAuthorizedTraceSchedule.toAnyActor
    {now : Time}
    {Method : Type}
    {env : ExecutionEnv} :
    ∀ {actors : List Actor} {start finish : GovState},
      FreshAuthorizedTraceSchedule now Method env actors start finish →
        FreshAuthorizedTraceAnyActor now Method env start finish
  | _, _, _, FreshAuthorizedTraceSchedule.nil state =>
      FreshAuthorizedTraceAnyActor.nil state
  | _, _, _, FreshAuthorizedTraceSchedule.cons step rest =>
      FreshAuthorizedTraceAnyActor.cons step
        (FreshAuthorizedTraceSchedule.toAnyActor rest)

/-- The fresh AnyActor projection commutes with forgetting freshness. -/
@[simp] theorem fresh_toAnyActor_toAuthorizedTraceAnyActor
    {now : Time}
    {Method : Type}
    {env : ExecutionEnv}
    {actor : Actor}
    {start finish : GovState}
    (trace : FreshAuthorizedTrace now Method env actor start finish) :
    FreshAuthorizedTraceAnyActor.toAuthorizedTraceAnyActor
        (FreshAuthorizedTrace.toAnyActor trace) =
      AuthorizedTrace.toAnyActor
        (FreshAuthorizedTrace.toAuthorizedTrace trace) := by
  induction trace with
  | nil _ =>
      rfl
  | cons _ _ ih =>
      simp [FreshAuthorizedTrace.toAnyActor,
        FreshAuthorizedTraceAnyActor.toAuthorizedTraceAnyActor,
        FreshAuthorizedTrace.toAuthorizedTrace,
        AuthorizedTrace.toAnyActor, ih]

/-- Fresh schedule AnyActor projection commutes with forgetting freshness. -/
@[simp] theorem fresh_schedule_toAnyActor_toAuthorizedTraceAnyActor
    {now : Time}
    {Method : Type}
    {env : ExecutionEnv}
    {actors : List Actor}
    {start finish : GovState}
    (trace : FreshAuthorizedTraceSchedule now Method env actors start finish) :
    FreshAuthorizedTraceAnyActor.toAuthorizedTraceAnyActor
        (FreshAuthorizedTraceSchedule.toAnyActor trace) =
      AuthorizedTraceSchedule.toAnyActor
        (FreshAuthorizedTraceSchedule.toAuthorizedTraceSchedule trace) := by
  induction trace with
  | nil _ =>
      rfl
  | cons _ _ ih =>
      simp [FreshAuthorizedTraceSchedule.toAnyActor,
        FreshAuthorizedTraceAnyActor.toAuthorizedTraceAnyActor,
        FreshAuthorizedTraceSchedule.toAuthorizedTraceSchedule,
        AuthorizedTraceSchedule.toAnyActor, ih]

/-- Fresh schedule AnyActor projection preserves the schedule step list. -/
@[simp] theorem anyActorTraceSteps_fresh_schedule_toAnyActor
    {now : Time}
    {Method : Type}
    {env : ExecutionEnv}
    {actors : List Actor}
    {start finish : GovState}
    (trace : FreshAuthorizedTraceSchedule now Method env actors start finish) :
    anyActorTraceSteps
        (FreshAuthorizedTraceAnyActor.toAuthorizedTraceAnyActor
          (FreshAuthorizedTraceSchedule.toAnyActor trace)) =
      scheduleTraceSteps
        (FreshAuthorizedTraceSchedule.toAuthorizedTraceSchedule trace) := by
  rw [fresh_schedule_toAnyActor_toAuthorizedTraceAnyActor]
  exact anyActorTraceSteps_schedule_toAnyActor
    (FreshAuthorizedTraceSchedule.toAuthorizedTraceSchedule trace)

/-- Fixed fresh scheduling agrees with the direct fresh AnyActor path. -/
@[simp] theorem fresh_toSchedule_toAnyActor_toAuthorizedTraceAnyActor
    {now : Time}
    {Method : Type}
    {env : ExecutionEnv}
    {actor : Actor}
    {start finish : GovState}
    (trace : FreshAuthorizedTrace now Method env actor start finish) :
    FreshAuthorizedTraceAnyActor.toAuthorizedTraceAnyActor
        (FreshAuthorizedTraceSchedule.toAnyActor
          (FreshAuthorizedTrace.toSchedule trace)) =
      FreshAuthorizedTraceAnyActor.toAuthorizedTraceAnyActor
        (FreshAuthorizedTrace.toAnyActor trace) := by
  rw [fresh_schedule_toAnyActor_toAuthorizedTraceAnyActor,
    fresh_toSchedule_toAuthorizedTraceSchedule, toSchedule_toAnyActor,
    fresh_toAnyActor_toAuthorizedTraceAnyActor]

/-- Fresh fixed-actor traces project to AnyActor traces without changing steps. -/
@[simp] theorem anyActorTraceSteps_fresh_toAnyActor
    {now : Time}
    {Method : Type}
    {env : ExecutionEnv}
    {actor : Actor}
    {start finish : GovState}
    (trace : FreshAuthorizedTrace now Method env actor start finish) :
    anyActorTraceSteps
        (FreshAuthorizedTraceAnyActor.toAuthorizedTraceAnyActor
          (FreshAuthorizedTrace.toAnyActor trace)) =
      traceSteps (FreshAuthorizedTrace.toAuthorizedTrace trace) := by
  rw [fresh_toAnyActor_toAuthorizedTraceAnyActor]
  exact anyActorTraceSteps_toAnyActor
    (FreshAuthorizedTrace.toAuthorizedTrace trace)

/-! ## Axiom-footprint receipts -/

#print axioms ObservationFreshAt
#print axioms fresh_dynamic_step_requires_authority
#print axioms fresh_dynamic_step_requires_fresh_observation
#print axioms stale_observation_cannot_discharge_current_obligation
#print axioms expired_observation_not_fresh
#print axioms not_yet_valid_observation_not_fresh
#print axioms incoherent_observation_not_fresh
#print axioms not_precedes_observation_not_fresh
#print axioms divergence_excessive_observation_not_fresh
#print axioms expired_observation_cannot_discharge_current_obligation
#print axioms not_yet_valid_observation_cannot_discharge_current_obligation
#print axioms incoherent_observation_cannot_discharge_current_obligation
#print axioms not_precedes_observation_cannot_discharge_current_obligation
#print axioms divergence_excessive_observation_cannot_discharge_current_obligation
#print axioms FreshAuthorizedTrace.toAuthorizedTrace
#print axioms FreshAuthorizedTraceSchedule
#print axioms FreshAuthorizedTrace.toSchedule
#print axioms FreshAuthorizedTraceSchedule.toAuthorizedTraceSchedule
#print axioms fresh_toSchedule_toAuthorizedTraceSchedule
#print axioms FreshAuthorizedTraceAnyActor
#print axioms FreshAuthorizedTraceAnyActor.toAuthorizedTraceAnyActor
#print axioms FreshAuthorizedTrace.toAnyActor
#print axioms FreshAuthorizedTraceSchedule.toAnyActor
#print axioms fresh_toAnyActor_toAuthorizedTraceAnyActor
#print axioms fresh_schedule_toAnyActor_toAuthorizedTraceAnyActor
#print axioms anyActorTraceSteps_fresh_schedule_toAnyActor
#print axioms fresh_toSchedule_toAnyActor_toAuthorizedTraceAnyActor
#print axioms anyActorTraceSteps_fresh_toAnyActor

end Admissibility.FreshnessDynamicTrace
