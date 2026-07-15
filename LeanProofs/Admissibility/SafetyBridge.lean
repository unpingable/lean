/-
  Custody-Class: ANNEX

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

  Actor-inertness decision (safety-axis kernel base). The base safety
  bridge is actor-inert: `bridge : σ → α → Prop`. Actor-relative
  evidence remains in `Allowed`; safety preservation is over the
  transition effect. An actor-sensitive extension requires an
  actor-indexed transition semantics or a separating formal model. If actor identity
  affects transition semantics, the transition relation itself must
  become actor-indexed (`run : σ → ρ → α → σ`) rather than smuggling
  actor-dependence through `bridge`. Reason: in the current safety-axis
  kernel `run : σ → α → σ` does not consume `ρ`, so an actor parameter in
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
      partial-order defended observable is an independent formal
      generalization, simply outside v0's chosen scope.
    * Preservation is a *floor* (`value st ≤ value (run st x)`:
      non-decrease). Strengthening to conservation (`=`) is a doctrinal
      choice a stricter env may make; the floor is the weaker, safer
      default and is what negates the strict-decrease wound.
    * Generic n-step trajectory composition (`bridgedTraj_preserves`)
      is now part of this substrate. The receipt-poison verdict-layer
      specialization (`SafetyTrajectory.lean`) carries the richer
      `SafeAuthorizedStepC` hop and provides the negative + no-lift
      results over the concrete miniature.
    * `bridge` is actor-inert by design (see Actor-inertness decision
      above). The actor-sensitive variant is `ActorSensitiveBridgeEnv`,
      named-but-not-implemented; it needs a separating formal model, not
      a downstream consumer.

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

/-! ### Per-hop step gates — actor is a field, not a type parameter

  Substrate fix (safety-axis kernel prep, canonicalization pass). A step
  records *who acted* as a field; the trajectory does not bind a
  single global actor. Single-actor trajectories remain expressible
  as a property (∀ hop, hop.actor = a) but are no longer the
  primitive substrate. Acid test: a two-hop path where hop 1 is
  authorized by actor A and hop 2 by actor B type-checks against
  these primitives without pretending one actor owns the path. -/

/--
  An authorized step: the per-hop record of "who did what, with what
  standing." No bridge witness. Used as the per-hop type of the
  authorized-but-possibly-unsafe trajectory.
-/
structure AuthStep {σ α ρ : Type}
    (E : SafetyEnv σ α ρ) (st : σ) where
  actor   : ρ
  act     : α
  allowed : E.Allowed st actor act

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
    (E : SafetyEnv σ α ρ) (st : σ) where
  actor   : ρ
  act     : α
  allowed : E.Allowed st actor act
  bridged : E.bridge st act

/-- Drop the bridge: a `SafeStep` is an `AuthStep` plus a bridge
    witness. -/
def SafeStep.toAuthStep {σ α ρ : Type} {E : SafetyEnv σ α ρ} {st : σ}
    (s : SafeStep E st) : AuthStep E st where
  actor   := s.actor
  act     := s.act
  allowed := s.allowed

/-- Every `SafeStep` preserves defended value. The boring projection
    through the bundle. -/
theorem safeStep_is_safe {σ α ρ : Type}
    (E : SafetyEnv σ α ρ) (st : σ)
    (s : SafeStep E st) :
    SafetyPreserving E st s.act :=
  E.preserves st s.act s.bridged

/-! ### Trajectories — state-threaded, per-hop actor

  Both families thread state through `E.run` and carry the real
  per-hop witness (the type *is* the proof that each hop is
  authorized at its own state). Actor lives in each hop — multi-actor
  trajectories are first-class; single-actor is a property over
  these, not a substrate constraint.

  Existential `Authorizable`-style projections would collapse the
  trajectory into "a sequence of independently-authorizable
  actions," erasing the per-hop witness. These inductives keep the
  actual authorized step at every hop.
-/

inductive AuthorizedTraj {σ α ρ : Type} (E : SafetyEnv σ α ρ) :
    σ → σ → Type where
  | nil (s : σ) : AuthorizedTraj E s s
  | cons {s : σ} (hop : AuthStep E s)
         {s' : σ} (rest : AuthorizedTraj E (E.run s hop.act) s') :
         AuthorizedTraj E s s'

inductive BridgedTraj {σ α ρ : Type} (E : SafetyEnv σ α ρ) :
    σ → σ → Type where
  | nil (s : σ) : BridgedTraj E s s
  | cons {s : σ} (hop : SafeStep E s)
         {s' : σ} (rest : BridgedTraj E (E.run s hop.act) s') :
         BridgedTraj E s s'

/-- Bridged trajectories are authorized trajectories — drop the
    bridge witness at each hop. Loop Capture is precisely an
    authorized trajectory that does not lift to a bridged one. -/
def BridgedTraj.toAuthorizedTraj {σ α ρ : Type} {E : SafetyEnv σ α ρ} :
    ∀ {s s' : σ}, BridgedTraj E s s' → AuthorizedTraj E s s'
  | _, _, .nil s => .nil s
  | _, _, .cons hop rest => .cons hop.toAuthStep rest.toAuthorizedTraj

/-- A bridged trajectory does not decrease defended value end to end.
    Structural recursion folding the per-hop discharge through `≤`. -/
theorem bridgedTraj_preserves {σ α ρ : Type} {E : SafetyEnv σ α ρ} :
    ∀ {s s' : σ}, BridgedTraj E s s' → E.value s ≤ E.value s'
  | _, _, .nil _ => Nat.le_refl _
  | s, _, .cons hop rest =>
      Nat.le_trans
        (E.preserves s hop.act hop.bridged)
        (bridgedTraj_preserves rest)

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

/-! ### Characterization layer — separation gap, collapse, obstruction

  The substrate primitives separate authorization from value
  preservation. These definitions and theorems characterize *when*
  that separation matters: when authorization fails to entail
  bridgeability, when the forgetful map has no right inverse, and
  when a bridge degenerates into "preservation restated."

  The point is to give the separation result named formal objects
  rather than examples-and-prose. The gap predicate says exactly
  what it means for authorization and bridge evidence to diverge.
  The collapse-iff theorem says authorization is enough for
  trajectories exactly when it is enough for every authorized hop.
  The obstruction theorem says the gap blocks any right inverse of
  the forgetful map. The maximal-bridge predicate fences off the
  degenerate corner where the bridge is preservation restated. -/

/-- The authorization-bridge gap: there exists an authorized step
    whose action is not bridged. The presence of the gap is what
    makes the separation non-vacuous; its absence collapses
    authorization into bridgeability. -/
def AuthorizationBridgeGap {σ α ρ : Type} (E : SafetyEnv σ α ρ) : Prop :=
  ∃ (s : σ) (x : AuthStep E s), ¬ E.bridge s x.act

/-- Authorization-preserves: every authorized step preserves the
    defended-value floor. When this holds, authorization carries the
    preservation evidence on its own and the bridge is no longer
    load-bearing. -/
def AuthPreserves {σ α ρ : Type} (E : SafetyEnv σ α ρ) : Prop :=
  ∀ {s : σ} (x : AuthStep E s), E.value s ≤ E.value (E.run s x.act)

/-- A bridge is *maximal* when it is logically equivalent to value
    preservation itself. A maximal bridge is preservation restated;
    it admits the trivializing critique that "the bridge is just the
    theorem conclusion." Useful structural bridges are sound but not
    necessarily complete. -/
def MaximalBridge {σ α ρ : Type} (E : SafetyEnv σ α ρ) : Prop :=
  ∀ (s : σ) (act : α), E.bridge s act ↔ E.value s ≤ E.value (E.run s act)

/-- A bridge is *complete* when every value-preserving action is
    bridged. Soundness is built into `SafetyEnv` via the `preserves`
    obligation. The interesting witness — and the one the receipt and
    ledger specimens carry — is sound-but-not-complete: a structural
    bridge that rejects value-preserving actions for lack of
    structural evidence. -/
def BridgeComplete {σ α ρ : Type} (E : SafetyEnv σ α ρ) : Prop :=
  ∀ (s : σ) (act : α), E.value s ≤ E.value (E.run s act) → E.bridge s act

/-- A *section* of the forgetful map from bridged to authorized
    trajectories: a function lifting any authorized trajectory to a
    bridged one whose erasure is the original. The existence of such
    a section would mean authorization carries enough to rebuild the
    bridge witness at every hop. The obstruction theorem below shows
    this fails in the presence of an authorization-bridge gap. -/
def HasForgetfulSection {σ α ρ : Type} (E : SafetyEnv σ α ρ) : Prop :=
  ∃ (lift : ∀ {s s' : σ}, AuthorizedTraj E s s' → BridgedTraj E s s'),
    ∀ {s s' : σ} (t : AuthorizedTraj E s s'),
      BridgedTraj.toAuthorizedTraj (lift t) = t

/-! ### Characterization theorems -/

/-- **Collapse characterization.** Trajectory-level preservation across
    all authorized trajectories is logically equivalent to per-hop
    authorized preservation. Authorization is enough for trajectories
    exactly when it is enough for every authorized step.

    Forward: a 1-hop authorized trajectory of any authorized step
    inherits trajectory preservation, giving hop preservation.
    Reverse: induction over the trajectory, folding hop preservation
    through `Nat.le_trans`. -/
theorem authorizedTraj_preserves_iff_authPreserves
    {σ α ρ : Type} (E : SafetyEnv σ α ρ) :
    (∀ {s s' : σ}, AuthorizedTraj E s s' → E.value s ≤ E.value s')
      ↔ AuthPreserves E := by
  constructor
  · intro htraj s x
    have t : AuthorizedTraj E s (E.run s x.act) :=
      AuthorizedTraj.cons x (AuthorizedTraj.nil _)
    exact htraj t
  · intro hpres
    intro s s' t
    induction t with
    | nil _ => exact Nat.le_refl _
    | cons hop _ ih => exact Nat.le_trans (hpres hop) ih

/-- **Empty-gap collapse.** When no authorization-bridge gap exists,
    every authorized step is bridged. Contrapositive of the gap
    definition; stated as a theorem so the boundary is named.
    (Term-mode `Classical.byContradiction` rather than `by_contra` —
    the latter lives in Mathlib and this module is core-Lean only.) -/
theorem no_gap_implies_authorized_steps_bridgeable
    {σ α ρ : Type} {E : SafetyEnv σ α ρ}
    (hno_gap : ¬ AuthorizationBridgeGap E)
    {s : σ} (x : AuthStep E s) : E.bridge s x.act :=
  Classical.byContradiction (fun hb => hno_gap ⟨s, x, hb⟩)

/-- **Obstruction (atomic form).** An authorized but unbridged step
    cannot be packaged as a `SafeStep`. This is the atomic obstruction
    behind the forgetful map having no general right inverse: the
    forgetful map `BridgedTraj.toAuthorizedTraj` projects each
    `SafeStep` hop to an `AuthStep` hop, but no `SafeStep` carries an
    unbridged action, so any 1-hop authorized trajectory whose hop is
    unbridged lies outside the forgetful map's image.

    Stating the obstruction at the step layer (rather than as the
    existence-of-section formulation) keeps the proof clean and the
    content explicit: the gap blocks lift at the smallest unit. -/
theorem no_safeStep_for_unbridged_authStep
    {σ α ρ : Type} {E : SafetyEnv σ α ρ}
    {s : σ} (x : AuthStep E s) (hbad : ¬ E.bridge s x.act) :
    ¬ ∃ (h : SafeStep E s), h.toAuthStep = x := by
  rintro ⟨h, heq⟩
  have hact : h.act = x.act := by
    have := congrArg AuthStep.act heq
    simpa [SafeStep.toAuthStep] using this
  exact hbad (hact ▸ h.bridged)

/-- **Obstruction at the gap level.** An authorization-bridge gap
    therefore witnesses the failure of any pointwise SafeStep lift:
    pick the witnessing unbridged authorized step, and no `SafeStep`
    erases to it. -/
theorem gap_blocks_safeStep_lift
    {σ α ρ : Type} {E : SafetyEnv σ α ρ}
    (hgap : AuthorizationBridgeGap E) :
    ∃ (s : σ) (x : AuthStep E s), ¬ ∃ (h : SafeStep E s), h.toAuthStep = x := by
  obtain ⟨s, x, hbad⟩ := hgap
  exact ⟨s, x, no_safeStep_for_unbridged_authStep x hbad⟩

/-- **Maximal bridge implies complete.** When the bridge is logically
    equivalent to preservation, every value-preserving action is
    bridged by construction. The other direction (sound bridges are
    not generally maximal) is the corner the witness modules occupy:
    structural bridges may reject value-preserving actions, so they
    are sound but not complete and hence not maximal. -/
theorem maximal_bridge_implies_complete
    {σ α ρ : Type} {E : SafetyEnv σ α ρ}
    (hmax : MaximalBridge E) : BridgeComplete E := by
  intro s act hpres
  exact (hmax s act).mpr hpres

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
     verdict layer via `SafeAuthorizedStepC`; brick 2 lifted the
     gate to trajectories — the generic per-hop-actor inductives
     and `bridgedTraj_preserves` now live in this substrate, with
     the verdict-layer specimens in `SafetyTrajectory.lean`.

  3. Bridge-candidate ratification. Choosing among
     witness-encapsulation / non-contamination / receipt-persistence
     requires a formal discriminator or countermodel plus an explicit
     doctrinal/custody choice. Runtime evidence may inform that review but
     is not permission to formalize a candidate and does not replace the
     discriminator. `nonContamination` (witness module) is the specimen,
     not the ratified choice.

  4. `ActorSensitiveBridgeEnv` — named deferred extension.

       structure ActorSensitiveBridgeEnv (σ α ρ : Type)
           extends SafetyEnv σ α ρ where
         actorBridge : σ → ρ → α → Prop
         actorBridge_sound :
           ∀ st a x, actorBridge st a x → bridge st x

     Not implemented. The current base is actor-inert; an actor-
     sensitive refinement needs a formal model in which actor identity
     is genuinely load-bearing. If actor identity actually changes the
     transition semantics, the right move is `run : σ → ρ → α → σ`,
     not a smuggled `ρ` in the predicate.
-/

end Admissibility.SafetyBridge
