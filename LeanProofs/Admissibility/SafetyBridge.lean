/-
  Admissibility — Safety bridge (candidate, non-binding).

  Frontier 1 (FRONTIERS.md): Admissibility ≠ Safety. The kernel can
  say a transition is *authorized* (`Execution.AuthorizedStep`); it
  cannot say an authorized transition *preserves defended value*.
  `AuthorizedNotSafe.lean` exhibits the wound; `AuthorizedNotSafeWitness.lean`
  witnesses it concretely. This module supplies the positive move named
  in `working/kernel-to-body-map.md` (Slice A): a conditional bridge,
  shaped as an analogue of `Corrective.RecoveryEnv`.

  The sentence this module warrants:

    safety = authorization ∧ bridge

  and — load-bearing — the generic safety theorem never consumes
  `Allowed`. `bridge_implies_safe` projects through `preserves` alone;
  authorization is carried in `SafeStep` because the surface API binds
  the two halves together, not because it contributes to the proof.
  Any concrete bridge must earn preservation through `preserves`, not
  by pointing back at authorization. That is the Frontier-1 thesis
  turned positive: "authorized garbage is still authorized" becomes
  "safety must be earned by a separate predicate, never inferred from
  authority."

  Actor-inertness decision (Calculus 2.0 base). The base safety bridge
  is actor-inert: `bridge : σ → α → Prop`. Actor-relative evidence
  remains in `Allowed`; safety preservation is over the transition
  effect. Actor-sensitive bridges are deferred until a concrete bridge
  candidate requires actor identity. If actor identity affects
  transition semantics, the transition relation itself must become
  actor-indexed (`run : σ → ρ → α → σ`) rather than smuggling
  actor-dependence through `bridge`. Reason: in the current calculus
  `run : σ → α → σ` does not consume `ρ`, so an actor parameter in
  `bridge` could only filter who gets to call the same transition
  safe — which is authorization wearing a safety mustache. The named
  deferred extension is `ActorSensitiveBridgeEnv` (see "Open" below);
  it is not implemented here.

  Obligation discipline (cf. `Corrective.CorrectiveMonotone`). The
  bridge's defining contract — *bridge entails value preservation* —
  is carried as a `preserves` field that any concrete `SafetyEnv`
  must discharge at construction. The abstract theorem is a
  projection through that field. Its content is not "safety holds"
  but "a compliant safety env must prove this shape, and the SafeStep
  gate makes that proof non-optional at the safety-relevant boundary."

  Candidate-neutral bridge slot. `bridge` is an abstract field. The
  three candidate fillings named in FRONTIERS.md Frontier 1 —
  witness-encapsulation lift (`WitnessInvariance.EncapsulatedWrt`),
  aggregator non-contamination at the action layer (WIF `D_A`), and
  receipt-persistence of consequence — are alternative inhabitants of
  this one slot. Picking among them is a doctrinal decision, not a
  Lean one; this module commits to none. `SafetyBridgeWitness.lean`
  inhabits the slot with the non-contamination candidate, as a
  demonstration that the obligation is dischargeable and does real
  discriminating work — not as a ratification of that candidate.

  Generic on purpose. Unlike `Corrective` (which is fixed over the
  kernel's `GovState`/`Step`), this module is parametric over the
  state/action/actor triple, because `value` and `bridge` are
  inherently external to the kernel — the env-supplies-the-strategy
  pattern is exactly `Derivation.DerivationEnv`. The kernel
  specialization is `SafetyEnv GovState Step Actor`; no inhabitant of
  that is claimed here (the concrete `value`/`bridge`/`preserves`
  triple is the open Slice-A work). The witness module inhabits the
  same structure at concrete miniature types — the parallel-miniature
  precedent is `CorrectiveBoundary.lean`.

  v0 simplifications (deferred, not hidden):
    * `value` codomain is `Nat`. Generalizing to `[Preorder V]` with a
      partial-order defended observable is mechanical; deferred until a
      forcing case needs a non-total order.
    * Preservation is a *floor* (`value st ≤ value (run st x)`:
      non-decrease). Strengthening to conservation (`=`) is a doctrinal
      choice a stricter env may make; the floor is the weaker, safer
      default and is what negates the strict-decrease wound.
    * Sequence composition beyond two steps is not built here; the
      two-step lemma establishes composability. A trajectory-indexed
      list theorem (analogue of `Corrective.corrective_sequence_monotone`)
      lives in `SafetyTrajectory.lean`.
    * `bridge` is actor-inert by design (see Actor-inertness decision
      above). The actor-sensitive variant is `ActorSensitiveBridgeEnv`,
      named-but-not-implemented; awaits a forcing-case candidate.

  Governor-neutral. Lean core only; no Mathlib, no sibling imports.
-/

namespace Admissibility.SafetyBridge

/-! ### Safety environment — the bridge slot plus its obligation -/

/--
  A safety environment over a `(state, action, actor)` triple.

  Fields:
  - `run`       — the transition (the kernel supplies `applyStep`).
  - `Allowed`   — the authorization relation (the kernel supplies
                  `StepAllowed`). Carried so the composed `SafeStep`
                  object holds authorization *and* safety; deliberately
                  *unused* by every safety theorem below.
  - `value`     — an externally-defined defended value. The kernel does
                  not constrain such functions; that lack of constraint
                  is the Frontier-1 wound.
  - `bridge`    — the candidate-neutral bridge predicate. Actor-inert
                  by design (see header decision note).
  - `preserves` — the obligation: any concrete env must prove that its
                  bridge entails value non-decrease. This is the field
                  that makes the bridge mean something.
-/
structure SafetyEnv (σ α ρ : Type) where
  run     : σ → α → σ
  Allowed : σ → ρ → α → Prop
  value   : σ → Nat
  bridge  : σ → α → Prop
  preserves :
    ∀ (st : σ) (x : α),
      bridge st x → value st ≤ value (run st x)

/-- Safety floor: the action does not strictly decrease defended value. -/
def SafetyPreserving {σ α ρ : Type}
    (E : SafetyEnv σ α ρ) (st : σ) (x : α) : Prop :=
  E.value st ≤ E.value (E.run st x)

/-! ### The conditional theorem — bridge carries safety; authorization is inert -/

/--
  The positive Frontier-1 statement: a bridged action preserves
  defended value. The proof projects `E.preserves`. Note the absence
  of any `Allowed` hypothesis — authorization is not an input to
  safety. That absence is the content.
-/
theorem bridge_implies_safe {σ α ρ : Type}
    (E : SafetyEnv σ α ρ) (st : σ) (x : α)
    (hb : E.bridge st x) :
    SafetyPreserving E st x :=
  E.preserves st x hb

/-! ### SafeStep — the gate (analogue of Execution.AuthorizedStep) -/

/--
  A safe step bundles an action with *both* its authorization witness
  (actor-relative) and its bridge witness (actor-inert). By
  construction there is no `SafeStep` without the bridge — so a
  safety-relevant execution path that takes a `SafeStep` cannot omit
  the safety proof, exactly as `AuthorizedStep` cannot omit either
  half of authorization and `RecoveryEnv` cannot omit the
  monotonicity witness.
-/
structure SafeStep {σ α ρ : Type}
    (E : SafetyEnv σ α ρ) (st : σ) (a : ρ) where
  act     : α
  allowed : E.Allowed st a act
  bridged : E.bridge st act

/-- Every `SafeStep` preserves defended value. The boring projection
    through the bundle. -/
theorem safeStep_is_safe {σ α ρ : Type}
    (E : SafetyEnv σ α ρ) (st : σ) (a : ρ)
    (s : SafeStep E st a) :
    SafetyPreserving E st s.act :=
  E.preserves st s.act s.bridged

/-! ### Composability — two bridged steps preserve value end to end -/

/--
  Minimal composition: a bridged step followed by a bridged step
  (the second evaluated at the intermediate state) preserves value
  across the pair. Establishes that the safety floor composes by
  transitivity of `≤`; the n-step trajectory theorem lives in
  `SafetyTrajectory.bridgedTraj_preserves`.
-/
theorem bridge_two_step_preserves {σ α ρ : Type}
    (E : SafetyEnv σ α ρ) (st : σ) (x y : α)
    (hx : E.bridge st x)
    (hy : E.bridge (E.run st x) y) :
    E.value st ≤ E.value (E.run (E.run st x) y) :=
  Nat.le_trans (E.preserves st x hx) (E.preserves (E.run st x) y hy)

/-
  Open (Slice A successors, pinned):

  1. Kernel inhabitant. `SafetyEnv GovState Step Actor` has no
     inhabitant here. Constructing one requires a concrete defended
     value over the kernel's (abstract) stores and a concrete bridge —
     the genuine open work. Until then this module pins the obligation
     shape; the witness module proves the shape is dischargeable.

  2. AuthorizedStep transfer — DONE. Brick 1
     (`AuthorizedStepNotSafe.lean` and its witness) settled the
     verdict-layer transfer and lifted the safety gate to the
     verdict layer via `SafeAuthorizedStepC`; brick 2
     (`SafetyTrajectory.lean`) lifted the gate to trajectories.

  3. Bridge-candidate ratification. Choosing among
     witness-encapsulation / non-contamination / receipt-persistence is
     deferred to doctrine. The forcing case is the first concrete
     consumer whose safety claim cannot be stated under one candidate
     but can under another. `nonContamination` (witness module) is the
     specimen, not the ratified choice.

  4. `ActorSensitiveBridgeEnv` — named deferred extension.

       structure ActorSensitiveBridgeEnv (σ α ρ : Type)
           extends SafetyEnv σ α ρ where
         actorBridge : σ → ρ → α → Prop
         actorBridge_sound :
           ∀ st a x, actorBridge st a x → bridge st x

     Not implemented. The current base is actor-inert; an actor-
     sensitive refinement waits on a bridge candidate that genuinely
     needs actor identity. If actor identity actually changes the
     transition semantics, the right move is `run : σ → ρ → α → σ`,
     not a smuggled `ρ` in the predicate.
-/

end Admissibility.SafetyBridge
