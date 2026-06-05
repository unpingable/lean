/-
  Custody-Class: ANNEX

  Admissibility — Composition (Slice 0: global-boundary process lift).

  Status: diagnostic. Not the calculus.

  Keeper:
    Under a sealed global boundary, every process is safe — because
    every config mutation still passes through the kernel `Step`
    relation. This file demonstrates that process syntax alone does
    NOT create a true calculus.

  Sharper:
    Adds a minimal process language (stop / expose-prefix / parallel)
    and a combined system semantics that pairs a process with a flat
    `Config`. The composition theorem proved here is intentionally
    stronger than compositional preservation: it holds for any
    process, not just compositions of "safe" components. That is the
    diagnostic — the safety hypotheses are not load-bearing, because
    the global boundary already does all the work.

    The first nontrivial composition-kernel theorem would have to
    make safety depend on local process boundaries and an admissible
    boundary-merge rule — and even that earns a propagation kernel,
    not a unified calculus. See `Admissibility/LocalBoundary.lean`
    for the experimental aperture toward that theorem.

  Companion prose
    Papers repo, `working/models/boundary-calculus/notes/locality-and-merge.md`.
    That note is the doctrine home of the discovery this file made
    formal; this file is the witness, not the doctrine.

  Scope fence
    - No restriction (ν), no replication.
    - No grades, no degradation, no failure, no cascade.
    - No bisimulation, no trace equivalence.
    - Boundary is global and identical for all components.
    - Not imported into `LeanProofs.lean` — sibling to the
      CrossBoundary* family, outside the no-sorry kernel chain
      (though this file is itself sorry-free).

  Custody
    Canonical anchoring of `Admissibility.Composition`. A definition
    matching this signature elsewhere does not inherit canonical
    anchoring from this file.
-/

import LeanProofs.Admissibility.CrossBoundaryExposure

namespace Admissibility.Composition

open CrossBoundaryExposure

/-- Minimal process language: stop, expose-prefix, parallel.
    No restriction. No replication. -/
inductive Process (Domain Failure : Type) where
  | stop
  | expose (e : Exposure Domain Failure) (cont : Process Domain Failure)
  | par (left right : Process Domain Failure)

/-- Labelled transition on processes. The only action that produces
    a label is `expose`, and it is gated by boundary authorization. -/
inductive StepP {Domain Failure : Type}
    (B : Boundary Domain) :
    Process Domain Failure → Action Domain Failure →
    Process Domain Failure → Prop where
  | expose :
      ∀ {e : Exposure Domain Failure} {cont : Process Domain Failure},
        B.authorized e.origin e.target = true →
        StepP B (Process.expose e cont) (Action.expose e) cont
  | parL :
      ∀ {P P' Q : Process Domain Failure} {α : Action Domain Failure},
        StepP B P α P' →
        StepP B (Process.par P Q) α (Process.par P' Q)
  | parR :
      ∀ {P Q Q' : Process Domain Failure} {α : Action Domain Failure},
        StepP B Q α Q' →
        StepP B (Process.par P Q) α (Process.par P Q')

/-- Combined system state: process term plus the current flat config. -/
structure SystemState (Domain Failure : Type) where
  proc : Process Domain Failure
  config : Config Domain Failure

/-- Initial system state from a process: empty config + the process. -/
def initialSystemState {Domain Failure : Type}
    [DecidableEq Domain] [DecidableEq Failure]
    (Q : Process Domain Failure) : SystemState Domain Failure :=
  ⟨Q, initialConfig Domain Failure⟩

/-- Combined step: process performs a `StepP` action; the config
    advances via the kernel `Step` with the matching action. The
    kernel step's `authorized` precondition is already enforced by
    `StepP.expose`, so the two layers cannot disagree. -/
inductive SystemStep {Domain Failure : Type}
    [DecidableEq Domain] [DecidableEq Failure]
    (B : Boundary Domain) :
    SystemState Domain Failure → SystemState Domain Failure → Prop where
  | step :
      ∀ {P P' : Process Domain Failure}
        {c c' : Config Domain Failure}
        {α : Action Domain Failure},
        StepP B P α P' →
        Step B c α c' →
        SystemStep B ⟨P, c⟩ ⟨P', c'⟩

/-- Reflexive-transitive closure of `SystemStep`. -/
inductive SystemReach {Domain Failure : Type}
    [DecidableEq Domain] [DecidableEq Failure]
    (B : Boundary Domain) :
    SystemState Domain Failure → SystemState Domain Failure → Prop where
  | refl : ∀ s, SystemReach B s s
  | tail :
      ∀ {s₀ s₁ s₂ : SystemState Domain Failure},
        SystemReach B s₀ s₁ → SystemStep B s₁ s₂ → SystemReach B s₀ s₂

/-- Process is safe under a global boundary if every reachable config
    from its initial state respects the partition. -/
def SafeProcess {Domain Failure : Type}
    [DecidableEq Domain] [DecidableEq Failure]
    (P_part : BoundaryPartition Domain)
    (B : Boundary Domain)
    (Q : Process Domain Failure) : Prop :=
  ∀ s : SystemState Domain Failure,
    SystemReach B (initialSystemState Q) s →
    NoInternalExternalExposure P_part s.config

/-- Diagnostic lemma: under a sealed global boundary, every process is
    safe. The process layer adds no new safety obligation, because the
    kernel `Step.expose` already enforces `authorized` and the
    sealed-boundary hypothesis rules out the Internal→External case. -/
theorem any_process_safe_under_sealed_boundary
    {Domain Failure : Type}
    [DecidableEq Domain] [DecidableEq Failure]
    (P_part : BoundaryPartition Domain)
    (B : Boundary Domain)
    (hNoExport : ∀ di dOut : Domain,
      P_part.Internal di → P_part.External dOut →
      B.authorized di dOut = false)
    (Q : Process Domain Failure)
    (s : SystemState Domain Failure)
    (hReach : SystemReach B (initialSystemState Q) s) :
    NoInternalExternalExposure P_part s.config := by
  induction hReach with
  | refl =>
      intro e he _hBad
      simp [initialSystemState, initialConfig] at he
  | tail _hReachPrev hStep ih =>
      cases hStep with
      | step _hStepP hStepK =>
          exact step_preserves_no_internal_external_exposure
            P_part B hNoExport ih hStepK

/-- **Composition theorem — global-boundary lift (diagnostic).**

    Under a sealed global boundary, the parallel composition of two
    safe processes is safe.

    The `_hSafeP` and `_hSafeQ` hypotheses are NOT used in the proof:
    `any_process_safe_under_sealed_boundary` already gives this
    conclusion for arbitrary processes. The theorem is intentionally
    stronger than compositional preservation.

    *Process syntax alone does not create a calculus. A propagation
    kernel begins where safety depends on the merge rule, not on the
    global oracle — and even that earns a kernel, not a unified
    calculus. See `Admissibility/LocalBoundary.lean` for the next
    aperture.* -/
theorem composition_preserves_safety_global_lift
    {Domain Failure : Type}
    [DecidableEq Domain] [DecidableEq Failure]
    (P_part : BoundaryPartition Domain)
    (B : Boundary Domain)
    (hNoExport : ∀ di dOut : Domain,
      P_part.Internal di → P_part.External dOut →
      B.authorized di dOut = false)
    (P Q : Process Domain Failure)
    (_hSafeP : SafeProcess P_part B P)
    (_hSafeQ : SafeProcess P_part B Q) :
    SafeProcess P_part B (Process.par P Q) := by
  intro s hReach
  exact any_process_safe_under_sealed_boundary
    P_part B hNoExport (Process.par P Q) s hReach

end Admissibility.Composition
