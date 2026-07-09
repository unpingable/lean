/-
  Custody-Class: ANNEX

  Admissibility.DynamicTrace -- state-threaded dynamic traces over the static
  admissibility execution bridge.

  This module builds a small dynamic calculus from the existing static
  admissibility kernels by making the hop payload an `Execution.AuthorizedStep`.
  It does not introduce a global `Admissible` judgment and does not compose
  static kernels by default: every hop carries the exact static witness it
  consumes.

  ANNEX, NOT PUBLIC SURFACE:
    * not imported by `AdmissibilityKernels.lean`;
    * not part of the 1.0 compatibility claim;
    * not a unified admissibility calculus;
    * not process semantics or runtime authority.
-/

import LeanProofs.Admissibility.Execution
import LeanProofs.Admissibility.Corrective

namespace Admissibility.DynamicTrace

open Admissibility.Authority
open Admissibility.StateTransition
open Admissibility.Execution

/-! ## Dynamic one-step wrapper -/

/--
  A dynamic step is one concrete state transition backed by the existing static
  `AuthorizedStep` bridge. The target state is not guessed: it must be exactly
  the state obtained by executing the authorized static step.
-/
structure DynamicStep
    (env : ExecutionEnv)
    (actor : Actor)
    (start finish : GovState) where
  authorized : AuthorizedStep env start actor
  finish_eq : finish = executeAuthorizedStep authorized

/-- Any `AuthorizedStep` yields the corresponding one-hop dynamic step. -/
def dynamicStepOfAuthorized
    {env : ExecutionEnv}
    {state : GovState}
    {actor : Actor}
    (step : AuthorizedStep env state actor) :
    DynamicStep env actor state (executeAuthorizedStep step) :=
  { authorized := step, finish_eq := rfl }

/-- Dynamic execution still requires mutation-side standing. -/
theorem dynamic_step_requires_stepAllowed
    {env : ExecutionEnv}
    {actor : Actor}
    {start finish : GovState}
    (step : DynamicStep env actor start finish) :
    StepAllowed start actor step.authorized.step :=
  step.authorized.stepAllowed

/-- Dynamic execution still requires claim-side authorization. -/
theorem dynamic_step_requires_authority
    {env : ExecutionEnv}
    {actor : Actor}
    {start finish : GovState}
    (step : DynamicStep env actor start finish) :
    stepAuthorityVerdict env start actor step.authorized.step =
      AuthorityVerdict.authorized :=
  step.authorized.authorityAuthorized

/--
  Revoked basis blocks the corresponding dynamic step. This is the static
  `Execution.revoked_basis_cannot_be_authorized_step` wall lifted through the
  dynamic wrapper.
-/
theorem revoked_basis_blocks_dynamic_step
    {env : ExecutionEnv}
    {state finish : GovState}
    {actor : Actor}
    {step : Step}
    (hrevoked :
      env.derivation.basis.basisRevoked
        state
        (env.claimForStep state actor step)) :
    ¬ ∃ dyn : DynamicStep env actor state finish,
        dyn.authorized.step = step := by
  intro h
  rcases h with ⟨dyn, hstep⟩
  exact revoked_basis_cannot_be_authorized_step hrevoked ⟨dyn.authorized, hstep⟩

/--
  Revoked invocation standing blocks the corresponding dynamic step. This is
  the static `Execution.revoked_standing_cannot_be_authorized_step` wall lifted
  through the dynamic wrapper.
-/
theorem revoked_standing_blocks_dynamic_step
    {env : ExecutionEnv}
    {state finish : GovState}
    {actor : Actor}
    {step : Step}
    (hrevoked :
      env.derivation.standing.standingRevoked
        state
        actor
        (env.claimForStep state actor step)) :
    ¬ ∃ dyn : DynamicStep env actor state finish,
        dyn.authorized.step = step := by
  intro h
  rcases h with ⟨dyn, hstep⟩
  exact revoked_standing_cannot_be_authorized_step hrevoked
    ⟨dyn.authorized, hstep⟩

/--
  Mutation standing alone does not create a dynamic step. If the claim-side
  verdict for the same static step is not `authorized`, no dynamic wrapper can
  exist, even when the mutation-side `StepAllowed` proof is available.
-/
theorem step_allowed_without_authority_blocks_dynamic_step
    {env : ExecutionEnv}
    {state finish : GovState}
    {actor : Actor}
    {step : Step}
    (_hallowed : StepAllowed state actor step)
    (hnotAuth :
      stepAuthorityVerdict env state actor step ≠ AuthorityVerdict.authorized) :
    ¬ ∃ dyn : DynamicStep env actor state finish,
        dyn.authorized.step = step := by
  intro h
  rcases h with ⟨dyn, hstep⟩
  have hauth :
      stepAuthorityVerdict env state actor step =
        AuthorityVerdict.authorized := by
    rw [← hstep]
    exact dyn.authorized.authorityAuthorized
  exact hnotAuth hauth

/-! ## State-threaded traces -/

/--
  A dynamic trace is a state-threaded sequence of dynamic steps. Its type is the
  proof that every hop supplied an `AuthorizedStep`; there is no constructor for
  an unwitnessed transition.
-/
inductive AuthorizedTrace
    (env : ExecutionEnv)
    (actor : Actor) :
    GovState → GovState → Type where
  | nil (state : GovState) : AuthorizedTrace env actor state state
  | cons
      {start mid finish : GovState}
      (step : DynamicStep env actor start mid)
      (rest : AuthorizedTrace env actor mid finish) :
      AuthorizedTrace env actor start finish

/-- A single static authorized step is a one-hop dynamic trace. -/
noncomputable def singletonTrace
    {env : ExecutionEnv}
    {state : GovState}
    {actor : Actor}
    (step : AuthorizedStep env state actor) :
    AuthorizedTrace env actor state (executeAuthorizedStep step) :=
  AuthorizedTrace.cons (dynamicStepOfAuthorized step)
    (AuthorizedTrace.nil (executeAuthorizedStep step))

/--
  The underlying static `Step`s in a dynamic trace, ordered exactly as they
  execute.
-/
def traceSteps
    {env : ExecutionEnv}
    {actor : Actor}
    {start finish : GovState}
    (trace : AuthorizedTrace env actor start finish) : List Step :=
  match trace with
  | AuthorizedTrace.nil _ => []
  | AuthorizedTrace.cons step rest =>
      step.authorized.step :: traceSteps rest


/-! ## Actor-indexed state-threaded traces -/

/--
  Actor-indexed traces do not grant authority to traces. They record that each
  hop independently satisfied the standing and authority predicates for the
  actor that performed that hop.
-/
inductive AuthorizedTraceAnyActor
    (env : ExecutionEnv) :
    GovState → GovState → Type where
  | nil (state : GovState) : AuthorizedTraceAnyActor env state state
  | cons
      {actor : Actor}
      {start mid finish : GovState}
      (step : DynamicStep env actor start mid)
      (rest : AuthorizedTraceAnyActor env mid finish) :
      AuthorizedTraceAnyActor env start finish

/-! ## Schedule-indexed state-threaded traces -/

/--
  A schedule-indexed trace records the exact actor sequence in its type. Each
  hop still carries its own `AuthorizedStep`; the schedule index is only a
  structural view of the actors that executed the hops.
-/
inductive AuthorizedTraceSchedule
    (env : ExecutionEnv) :
    List Actor → GovState → GovState → Type where
  | nil (state : GovState) :
      AuthorizedTraceSchedule env [] state state
  | cons
      {actor : Actor}
      {actors : List Actor}
      {start mid finish : GovState}
      (step : DynamicStep env actor start mid)
      (rest : AuthorizedTraceSchedule env actors mid finish) :
      AuthorizedTraceSchedule env (actor :: actors) start finish

/-- A single static authorized step is a one-hop schedule-indexed trace. -/
noncomputable def singletonTraceSchedule
    {env : ExecutionEnv}
    {state : GovState}
    {actor : Actor}
    (step : AuthorizedStep env state actor) :
    AuthorizedTraceSchedule env [actor] state (executeAuthorizedStep step) :=
  AuthorizedTraceSchedule.cons (dynamicStepOfAuthorized step)
    (AuthorizedTraceSchedule.nil (executeAuthorizedStep step))

/-- View a fixed-actor trace as a trace whose schedule repeats that actor. -/
def AuthorizedTrace.toSchedule
    {env : ExecutionEnv}
    {actor : Actor} :
    ∀ {start finish : GovState},
      (trace : AuthorizedTrace env actor start finish) →
        AuthorizedTraceSchedule env
          (List.replicate (traceSteps trace).length actor) start finish
  | _, _, AuthorizedTrace.nil state =>
      AuthorizedTraceSchedule.nil state
  | _, _, AuthorizedTrace.cons step rest =>
      AuthorizedTraceSchedule.cons step
        (AuthorizedTrace.toSchedule rest)

/-- Forget the schedule index and view a trace as locally actor-indexed. -/
def AuthorizedTraceSchedule.toAnyActor
    {env : ExecutionEnv} :
    ∀ {actors : List Actor} {start finish : GovState},
      AuthorizedTraceSchedule env actors start finish →
        AuthorizedTraceAnyActor env start finish
  | _, _, _, AuthorizedTraceSchedule.nil state =>
      AuthorizedTraceAnyActor.nil state
  | _, _, _, AuthorizedTraceSchedule.cons step rest =>
      AuthorizedTraceAnyActor.cons step
        (AuthorizedTraceSchedule.toAnyActor rest)

/-- Forget the single fixed actor and view a trace as locally actor-indexed. -/
def AuthorizedTrace.toAnyActor
    {env : ExecutionEnv}
    {actor : Actor} :
    ∀ {start finish : GovState},
      AuthorizedTrace env actor start finish →
        AuthorizedTraceAnyActor env start finish
  | _, _, AuthorizedTrace.nil state =>
      AuthorizedTraceAnyActor.nil state
  | _, _, AuthorizedTrace.cons step rest =>
      AuthorizedTraceAnyActor.cons step
        (AuthorizedTrace.toAnyActor rest)

/-- Scheduling a fixed-actor trace and then forgetting the schedule is neutral. -/
@[simp] theorem toSchedule_toAnyActor
    {env : ExecutionEnv}
    {actor : Actor}
    {start finish : GovState}
    (trace : AuthorizedTrace env actor start finish) :
    AuthorizedTraceSchedule.toAnyActor (AuthorizedTrace.toSchedule trace) =
      AuthorizedTrace.toAnyActor trace := by
  induction trace with
  | nil _ =>
      rfl
  | cons _ _ ih =>
      simp [AuthorizedTrace.toSchedule, AuthorizedTraceSchedule.toAnyActor,
        AuthorizedTrace.toAnyActor, ih]

/-- A single static authorized step is a one-hop AnyActor dynamic trace. -/
noncomputable def singletonTraceAnyActor
    {env : ExecutionEnv}
    {state : GovState}
    {actor : Actor}
    (step : AuthorizedStep env state actor) :
    AuthorizedTraceAnyActor env state (executeAuthorizedStep step) :=
  AuthorizedTraceAnyActor.cons (dynamicStepOfAuthorized step)
    (AuthorizedTraceAnyActor.nil (executeAuthorizedStep step))

/-- One projected hop from an AnyActor trace, preserving its local actor. -/
structure TraceHop (env : ExecutionEnv) where
  actor : Actor
  start : GovState
  finish : GovState
  step : DynamicStep env actor start finish

/-- Package a dynamic step as a projected hop. -/
def traceHopOfDynamicStep
    {env : ExecutionEnv}
    {actor : Actor}
    {start finish : GovState}
    (step : DynamicStep env actor start finish) :
    TraceHop env :=
  { actor := actor, start := start, finish := finish, step := step }

/-- The underlying static `Step`s in an AnyActor trace, in execution order. -/
def anyActorTraceSteps
    {env : ExecutionEnv} :
    ∀ {start finish : GovState},
      AuthorizedTraceAnyActor env start finish → List Step
  | _, _, AuthorizedTraceAnyActor.nil _ => []
  | _, _, AuthorizedTraceAnyActor.cons step rest =>
      step.authorized.step :: anyActorTraceSteps rest

/-- The underlying static `Step`s in a schedule-indexed trace, in order. -/
def scheduleTraceSteps
    {env : ExecutionEnv} :
    ∀ {actors : List Actor} {start finish : GovState},
      AuthorizedTraceSchedule env actors start finish → List Step
  | _, _, _, AuthorizedTraceSchedule.nil _ => []
  | _, _, _, AuthorizedTraceSchedule.cons step rest =>
      step.authorized.step :: scheduleTraceSteps rest

/-- Forgetting the schedule preserves the underlying static step list. -/
@[simp] theorem anyActorTraceSteps_schedule_toAnyActor
    {env : ExecutionEnv}
    {actors : List Actor}
    {start finish : GovState}
    (trace : AuthorizedTraceSchedule env actors start finish) :
    anyActorTraceSteps (AuthorizedTraceSchedule.toAnyActor trace) =
      scheduleTraceSteps trace := by
  induction trace with
  | nil _ =>
      rfl
  | cons _ _ ih =>
      simp [AuthorizedTraceSchedule.toAnyActor, anyActorTraceSteps,
        scheduleTraceSteps, ih]

/-- The projected dynamic hops in an AnyActor trace, in execution order. -/
def anyActorTraceHops
    {env : ExecutionEnv} :
    ∀ {start finish : GovState},
      AuthorizedTraceAnyActor env start finish → List (TraceHop env)
  | _, _, AuthorizedTraceAnyActor.nil _ => []
  | _, _, AuthorizedTraceAnyActor.cons step rest =>
      traceHopOfDynamicStep step :: anyActorTraceHops rest

/-- The projected dynamic hops in a schedule-indexed trace, in order. -/
def scheduleTraceHops
    {env : ExecutionEnv} :
    ∀ {actors : List Actor} {start finish : GovState},
      AuthorizedTraceSchedule env actors start finish → List (TraceHop env)
  | _, _, _, AuthorizedTraceSchedule.nil _ => []
  | _, _, _, AuthorizedTraceSchedule.cons step rest =>
      traceHopOfDynamicStep step :: scheduleTraceHops rest

/-- Forgetting the schedule preserves the projected dynamic hops. -/
@[simp] theorem anyActorTraceHops_schedule_toAnyActor
    {env : ExecutionEnv}
    {actors : List Actor}
    {start finish : GovState}
    (trace : AuthorizedTraceSchedule env actors start finish) :
    anyActorTraceHops (AuthorizedTraceSchedule.toAnyActor trace) =
      scheduleTraceHops trace := by
  induction trace with
  | nil _ =>
      rfl
  | cons _ _ ih =>
      simp [AuthorizedTraceSchedule.toAnyActor, anyActorTraceHops,
        scheduleTraceHops, ih]

/-- The actors responsible for the hops in an AnyActor trace, in order. -/
def anyActorTraceActors
    {env : ExecutionEnv}
    {start finish : GovState}
    (trace : AuthorizedTraceAnyActor env start finish) : List Actor :=
  (anyActorTraceHops trace).map (fun hop => hop.actor)

/-- The actor schedule recorded in the type, as a value-level list. -/
def scheduleTraceActors
    {env : ExecutionEnv}
    {actors : List Actor}
    {start finish : GovState}
    (_trace : AuthorizedTraceSchedule env actors start finish) :
    List Actor :=
  actors

/-- The value-level schedule view is exactly the type-level schedule. -/
@[simp] theorem scheduleTraceActors_eq_schedule
    {env : ExecutionEnv}
    {actors : List Actor}
    {start finish : GovState}
    (trace : AuthorizedTraceSchedule env actors start finish) :
    scheduleTraceActors trace = actors :=
  rfl

/-- Projected schedule hops carry exactly the actors recorded in the schedule. -/
@[simp] theorem scheduleTraceHops_actors
    {env : ExecutionEnv}
    {actors : List Actor}
    {start finish : GovState}
    (trace : AuthorizedTraceSchedule env actors start finish) :
    (scheduleTraceHops trace).map (fun hop => hop.actor) = actors := by
  induction trace with
  | nil _ =>
      rfl
  | cons _ _ ih =>
      simp [scheduleTraceHops, traceHopOfDynamicStep, ih]

/-- Forgetting the schedule preserves the actor list recorded by the schedule. -/
@[simp] theorem anyActorTraceActors_schedule_toAnyActor
    {env : ExecutionEnv}
    {actors : List Actor}
    {start finish : GovState}
    (trace : AuthorizedTraceSchedule env actors start finish) :
    anyActorTraceActors (AuthorizedTraceSchedule.toAnyActor trace) = actors := by
  simp [anyActorTraceActors, anyActorTraceHops_schedule_toAnyActor,
    scheduleTraceHops_actors trace]

/-- Filter projected hops by actor, requiring equality only at this view. -/
def traceHopsByActor
    {env : ExecutionEnv}
    [DecidableEq Actor]
    (actor : Actor) :
    List (TraceHop env) → List (TraceHop env)
  | [] => []
  | hop :: rest =>
      if hop.actor = actor then
        hop :: traceHopsByActor actor rest
      else
        traceHopsByActor actor rest

/-- Projected dynamic hops performed by the selected actor. -/
def anyActorTraceHopsByActor
    {env : ExecutionEnv}
    [DecidableEq Actor]
    {start finish : GovState}
    (actor : Actor)
    (trace : AuthorizedTraceAnyActor env start finish) :
    List (TraceHop env) :=
  traceHopsByActor actor (anyActorTraceHops trace)

/-- Any projected AnyActor hop carries its own mutation-side standing. -/
theorem anyActor_trace_hop_requires_stepAllowed
    {env : ExecutionEnv}
    {start finish : GovState}
    {trace : AuthorizedTraceAnyActor env start finish}
    {hop : TraceHop env}
    (_hmem : hop ∈ anyActorTraceHops trace) :
    StepAllowed hop.start hop.actor hop.step.authorized.step :=
  dynamic_step_requires_stepAllowed hop.step

/-- Any projected AnyActor hop carries its own claim-side authorization. -/
theorem anyActor_trace_hop_requires_authority
    {env : ExecutionEnv}
    {start finish : GovState}
    {trace : AuthorizedTraceAnyActor env start finish}
    {hop : TraceHop env}
    (_hmem : hop ∈ anyActorTraceHops trace) :
    stepAuthorityVerdict env hop.start hop.actor hop.step.authorized.step =
      AuthorityVerdict.authorized :=
  dynamic_step_requires_authority hop.step

/-- Filtering projected hops by actor returns only hops for that actor. -/
theorem traceHopsByActor_actor
    {env : ExecutionEnv}
    [DecidableEq Actor]
    (actor : Actor)
    (hops : List (TraceHop env))
    {hop : TraceHop env}
    (hmem : hop ∈ traceHopsByActor actor hops) :
    hop.actor = actor := by
  induction hops with
  | nil =>
      simp [traceHopsByActor] at hmem
  | cons head rest ih =>
      by_cases hhead : head.actor = actor
      · simp [traceHopsByActor, hhead] at hmem
        rcases hmem with hmem | hmem
        · rw [hmem]
          exact hhead
        · exact ih hmem
      · simp [traceHopsByActor, hhead] at hmem
        exact ih hmem

/-- Filtering AnyActor trace hops by actor returns only hops for that actor. -/
theorem anyActorTraceHopsByActor_actor
    {env : ExecutionEnv}
    [DecidableEq Actor]
    {start finish : GovState}
    (actor : Actor)
    (trace : AuthorizedTraceAnyActor env start finish)
    {hop : TraceHop env}
    (hmem : hop ∈ anyActorTraceHopsByActor actor trace) :
    hop.actor = actor :=
  traceHopsByActor_actor actor (anyActorTraceHops trace) hmem

/-! ## Static trace projection -/

/-- Forgetting the fixed actor preserves the underlying static step list. -/
@[simp] theorem anyActorTraceSteps_toAnyActor
    {env : ExecutionEnv}
    {actor : Actor}
    {start finish : GovState}
    (trace : AuthorizedTrace env actor start finish) :
    anyActorTraceSteps (AuthorizedTrace.toAnyActor trace) =
      traceSteps trace := by
  induction trace with
  | nil _ =>
      rfl
  | cons _ _ ih =>
      simp [AuthorizedTrace.toAnyActor, anyActorTraceSteps, traceSteps, ih]

/--
  Scheduling a fixed-actor trace and then forgetting the schedule preserves the
  same static step view as the direct AnyActor projection.
-/
@[simp] theorem anyActorTraceSteps_toSchedule_toAnyActor
    {env : ExecutionEnv}
    {actor : Actor}
    {start finish : GovState}
    (trace : AuthorizedTrace env actor start finish) :
    anyActorTraceSteps
        (AuthorizedTraceSchedule.toAnyActor
          (AuthorizedTrace.toSchedule trace)) =
      traceSteps trace := by
  rw [toSchedule_toAnyActor]
  exact anyActorTraceSteps_toAnyActor trace

/--
  Scheduling a fixed-actor trace and then forgetting the schedule preserves the
  same projected hop view as the direct AnyActor projection.
-/
@[simp] theorem anyActorTraceHops_toSchedule_toAnyActor
    {env : ExecutionEnv}
    {actor : Actor}
    {start finish : GovState}
    (trace : AuthorizedTrace env actor start finish) :
    anyActorTraceHops
        (AuthorizedTraceSchedule.toAnyActor
          (AuthorizedTrace.toSchedule trace)) =
      anyActorTraceHops (AuthorizedTrace.toAnyActor trace) := by
  rw [toSchedule_toAnyActor]

/-- Predicate over traces whose every hop is corrective. -/
def CorrectiveTrace
    {env : ExecutionEnv}
    {actor : Actor}
    {start finish : GovState}
    (trace : AuthorizedTrace env actor start finish) : Prop :=
  ∀ step ∈ traceSteps trace, Corrective.IsCorrective step

/-- Unpack a corrective cons trace into its head and tail obligations. -/
theorem corrective_trace_cons_iff
    {env : ExecutionEnv}
    {actor : Actor}
    {start mid finish : GovState}
    (step : DynamicStep env actor start mid)
    (rest : AuthorizedTrace env actor mid finish) :
    CorrectiveTrace (AuthorizedTrace.cons step rest) ↔
      Corrective.IsCorrective step.authorized.step ∧ CorrectiveTrace rest := by
  constructor
  · intro h
    constructor
    · exact h step.authorized.step (by simp [traceSteps])
    · intro s hs
      exact h s (by simp [traceSteps, hs])
  · intro h s hs
    rcases h with ⟨hstep, hrest⟩
    simp [traceSteps] at hs
    rcases hs with hs | hs
    · rw [hs]
      exact hstep
    · exact hrest s hs


/-- Predicate over AnyActor traces whose every hop is corrective. -/
def CorrectiveTraceAnyActor
    {env : ExecutionEnv}
    {start finish : GovState}
    (trace : AuthorizedTraceAnyActor env start finish) : Prop :=
  ∀ step ∈ anyActorTraceSteps trace, Corrective.IsCorrective step

/-- Corrective fixed-actor traces project exactly to corrective AnyActor traces. -/
@[simp] theorem correctiveTraceAnyActor_toAnyActor_iff
    {env : ExecutionEnv}
    {actor : Actor}
    {start finish : GovState}
    (trace : AuthorizedTrace env actor start finish) :
    CorrectiveTraceAnyActor (AuthorizedTrace.toAnyActor trace) ↔
      CorrectiveTrace trace := by
  unfold CorrectiveTraceAnyActor CorrectiveTrace
  rw [anyActorTraceSteps_toAnyActor trace]

/-- Forward form of `correctiveTraceAnyActor_toAnyActor_iff`. -/
theorem correctiveTrace_toAnyActor
    {env : ExecutionEnv}
    {actor : Actor}
    {start finish : GovState}
    {trace : AuthorizedTrace env actor start finish} :
    CorrectiveTrace trace →
      CorrectiveTraceAnyActor (AuthorizedTrace.toAnyActor trace) :=
  (correctiveTraceAnyActor_toAnyActor_iff trace).mpr

/-- Unpack a corrective AnyActor cons trace into head and tail obligations. -/
theorem corrective_anyActor_trace_cons_iff
    {env : ExecutionEnv}
    {actor : Actor}
    {start mid finish : GovState}
    (step : DynamicStep env actor start mid)
    (rest : AuthorizedTraceAnyActor env mid finish) :
    CorrectiveTraceAnyActor (AuthorizedTraceAnyActor.cons step rest) ↔
      Corrective.IsCorrective step.authorized.step ∧
        CorrectiveTraceAnyActor rest := by
  constructor
  · intro h
    constructor
    · exact h step.authorized.step (by simp [anyActorTraceSteps])
    · intro s hs
      exact h s (by simp [anyActorTraceSteps, hs])
  · intro h s hs
    rcases h with ⟨hstep, hrest⟩
    simp [anyActorTraceSteps] at hs
    rcases hs with hs | hs
    · rw [hs]
      exact hstep
    · exact hrest s hs

/-! ## Non-amendment preservation -/

/-- The step kinds that cannot touch `PolicyStore`. -/
def NonAmendStep : Step → Prop
  | Step.recordReceipt _ => True
  | Step.declarePolicyGap _ => True
  | Step.recordRevocation _ => True
  | Step.amendPolicy _ => False

/--
  Static authorized non-amendment steps preserve `PolicyStore`. This packages
  the three existing store-isolation theorems behind the `NonAmendStep`
  predicate.
-/
theorem authorized_non_amend_step_preserves_policy
    {env : ExecutionEnv}
    {state : GovState}
    {actor : Actor}
    (step : AuthorizedStep env state actor)
    (h : NonAmendStep step.step) :
    (executeAuthorizedStep step).policyStore = state.policyStore := by
  cases hstep : step.step with
  | recordReceipt r =>
      exact authorized_record_receipt_does_not_amend_policy r step hstep
  | declarePolicyGap g =>
      exact authorized_declare_policy_gap_does_not_amend_policy g step hstep
  | recordRevocation rv =>
      exact authorized_record_revocation_does_not_amend_policy rv step hstep
  | amendPolicy p =>
      simp [NonAmendStep, hstep] at h

/-- A dynamic non-amendment step preserves `PolicyStore`. -/
theorem dynamic_non_amend_step_preserves_policy
    {env : ExecutionEnv}
    {actor : Actor}
    {start finish : GovState}
    (step : DynamicStep env actor start finish)
    (h : NonAmendStep step.authorized.step) :
    finish.policyStore = start.policyStore := by
  rw [step.finish_eq]
  exact authorized_non_amend_step_preserves_policy step.authorized h

/-- Predicate over traces whose every hop is a non-amendment step. -/
inductive NonAmendAuthorizedTrace
    {env : ExecutionEnv}
    {actor : Actor} :
    {start finish : GovState} →
      AuthorizedTrace env actor start finish → Prop where
  | nil (state : GovState) :
      NonAmendAuthorizedTrace (AuthorizedTrace.nil (env := env) (actor := actor) state)
  | cons
      {start mid finish : GovState}
      {step : DynamicStep env actor start mid}
      {rest : AuthorizedTrace env actor mid finish}
      (hstep : NonAmendStep step.authorized.step)
      (hrest : NonAmendAuthorizedTrace rest) :
      NonAmendAuthorizedTrace (AuthorizedTrace.cons step rest)

/--
  End-to-end preservation: a trace made only of authorized non-amendment hops
  cannot mutate `PolicyStore`.
-/
theorem non_amend_trace_preserves_policy
    {env : ExecutionEnv}
    {actor : Actor}
    {start finish : GovState}
    {trace : AuthorizedTrace env actor start finish}
    (h : NonAmendAuthorizedTrace trace) :
    finish.policyStore = start.policyStore := by
  induction h with
  | nil _ =>
      rfl
  | cons hstep _ ih =>
      exact ih.trans (dynamic_non_amend_step_preserves_policy _ hstep)


/-- Predicate over AnyActor traces whose every hop is a non-amendment step. -/
inductive NonAmendAuthorizedTraceAnyActor
    {env : ExecutionEnv} :
    {start finish : GovState} →
      AuthorizedTraceAnyActor env start finish → Prop where
  | nil (state : GovState) :
      NonAmendAuthorizedTraceAnyActor
        (AuthorizedTraceAnyActor.nil (env := env) state)
  | cons
      {actor : Actor}
      {start mid finish : GovState}
      {step : DynamicStep env actor start mid}
      {rest : AuthorizedTraceAnyActor env mid finish}
      (hstep : NonAmendStep step.authorized.step)
      (hrest : NonAmendAuthorizedTraceAnyActor rest) :
      NonAmendAuthorizedTraceAnyActor
        (AuthorizedTraceAnyActor.cons step rest)

/-- Non-amendment fixed-actor traces project to non-amendment AnyActor traces. -/
theorem nonAmendAuthorizedTrace_toAnyActor
    {env : ExecutionEnv}
    {actor : Actor}
    {start finish : GovState}
    {trace : AuthorizedTrace env actor start finish}
    (h : NonAmendAuthorizedTrace trace) :
    NonAmendAuthorizedTraceAnyActor (AuthorizedTrace.toAnyActor trace) := by
  induction h with
  | nil state =>
      exact NonAmendAuthorizedTraceAnyActor.nil state
  | cons hstep _ ih =>
      exact NonAmendAuthorizedTraceAnyActor.cons hstep ih

/--
  End-to-end preservation: an AnyActor trace made only of authorized
  non-amendment hops cannot mutate `PolicyStore`.
-/
theorem non_amend_anyActor_trace_preserves_policy
    {env : ExecutionEnv}
    {start finish : GovState}
    {trace : AuthorizedTraceAnyActor env start finish}
    (h : NonAmendAuthorizedTraceAnyActor trace) :
    finish.policyStore = start.policyStore := by
  induction h with
  | nil _ =>
      rfl
  | cons hstep _ ih =>
      exact ih.trans (dynamic_non_amend_step_preserves_policy _ hstep)

/-! ## Corrective monotonicity over dynamic traces -/

/--
  A single authorized dynamic corrective step preserves the static corrective
  monotonicity bound, relative to the supplied derivation obligation.
-/
theorem corrective_dynamic_step_preserves_static_monotonicity_bound
    {env : ExecutionEnv}
    {actor : Actor}
    {start finish : GovState}
    (cm : Corrective.CorrectiveMonotone env.derivation)
    (step : DynamicStep env actor start finish)
    (hc : Corrective.IsCorrective step.authorized.step) :
    Corrective.WeaklyLessPermissive env.derivation finish start := by
  rw [step.finish_eq]
  simpa [executeAuthorizedStep] using
    Corrective.corrective_monotone
      cm start step.authorized.step hc

/--
  A trace made only of authorized corrective hops cannot expand the permissive
  surface beyond its start state.
-/
theorem corrective_authorized_trace_preserves_static_monotonicity_bound
    {env : ExecutionEnv}
    {actor : Actor}
    {start finish : GovState}
    (cm : Corrective.CorrectiveMonotone env.derivation)
    (trace : AuthorizedTrace env actor start finish)
    (h : CorrectiveTrace trace) :
    Corrective.WeaklyLessPermissive env.derivation finish start := by
  induction trace with
  | nil state =>
      exact Corrective.weakly_less_permissive_refl env.derivation state
  | cons step rest ih =>
      have hsplit := (corrective_trace_cons_iff step rest).mp h
      rcases hsplit with ⟨hstep, hrest⟩
      have hhead :
          Corrective.WeaklyLessPermissive
            env.derivation _ _ :=
        corrective_dynamic_step_preserves_static_monotonicity_bound
          cm step hstep
      have htail :
          Corrective.WeaklyLessPermissive
            env.derivation _ _ :=
        ih hrest
      exact Corrective.weakly_less_permissive_trans htail hhead


/--
  An AnyActor trace made only of authorized corrective hops cannot expand the
  permissive surface beyond its start state.
-/
theorem corrective_authorized_anyActor_trace_preserves_static_monotonicity_bound
    {env : ExecutionEnv}
    {start finish : GovState}
    (cm : Corrective.CorrectiveMonotone env.derivation)
    (trace : AuthorizedTraceAnyActor env start finish)
    (h : CorrectiveTraceAnyActor trace) :
    Corrective.WeaklyLessPermissive env.derivation finish start := by
  induction trace with
  | nil state =>
      exact Corrective.weakly_less_permissive_refl env.derivation state
  | cons step rest ih =>
      have hsplit := (corrective_anyActor_trace_cons_iff step rest).mp h
      rcases hsplit with ⟨hstep, hrest⟩
      have hhead :
          Corrective.WeaklyLessPermissive
            env.derivation _ _ :=
        corrective_dynamic_step_preserves_static_monotonicity_bound
          cm step hstep
      have htail :
          Corrective.WeaklyLessPermissive
            env.derivation _ _ :=
        ih hrest
      exact Corrective.weakly_less_permissive_trans htail hhead

/-! ## Axiom-footprint receipts -/

#print axioms dynamic_step_requires_stepAllowed
#print axioms dynamic_step_requires_authority
#print axioms revoked_basis_blocks_dynamic_step
#print axioms revoked_standing_blocks_dynamic_step
#print axioms step_allowed_without_authority_blocks_dynamic_step
#print axioms singletonTrace
#print axioms AuthorizedTraceAnyActor
#print axioms AuthorizedTraceSchedule
#print axioms singletonTraceSchedule
#print axioms AuthorizedTrace.toSchedule
#print axioms AuthorizedTraceSchedule.toAnyActor
#print axioms AuthorizedTrace.toAnyActor
#print axioms toSchedule_toAnyActor
#print axioms singletonTraceAnyActor
#print axioms TraceHop
#print axioms traceHopOfDynamicStep
#print axioms anyActorTraceSteps
#print axioms scheduleTraceSteps
#print axioms anyActorTraceSteps_schedule_toAnyActor
#print axioms anyActorTraceHops
#print axioms scheduleTraceHops
#print axioms anyActorTraceHops_schedule_toAnyActor
#print axioms anyActorTraceActors
#print axioms scheduleTraceActors
#print axioms scheduleTraceActors_eq_schedule
#print axioms scheduleTraceHops_actors
#print axioms anyActorTraceActors_schedule_toAnyActor
#print axioms traceHopsByActor
#print axioms anyActorTraceHopsByActor
#print axioms anyActor_trace_hop_requires_stepAllowed
#print axioms anyActor_trace_hop_requires_authority
#print axioms traceHopsByActor_actor
#print axioms anyActorTraceHopsByActor_actor
#print axioms anyActorTraceSteps_toAnyActor
#print axioms anyActorTraceSteps_toSchedule_toAnyActor
#print axioms anyActorTraceHops_toSchedule_toAnyActor
#print axioms authorized_non_amend_step_preserves_policy
#print axioms dynamic_non_amend_step_preserves_policy
#print axioms non_amend_trace_preserves_policy
#print axioms NonAmendAuthorizedTraceAnyActor
#print axioms nonAmendAuthorizedTrace_toAnyActor
#print axioms non_amend_anyActor_trace_preserves_policy
#print axioms traceSteps
#print axioms CorrectiveTrace
#print axioms CorrectiveTraceAnyActor
#print axioms correctiveTraceAnyActor_toAnyActor_iff
#print axioms correctiveTrace_toAnyActor
#print axioms corrective_anyActor_trace_cons_iff
#print axioms corrective_dynamic_step_preserves_static_monotonicity_bound
#print axioms corrective_authorized_trace_preserves_static_monotonicity_bound
#print axioms corrective_authorized_anyActor_trace_preserves_static_monotonicity_bound


end Admissibility.DynamicTrace
