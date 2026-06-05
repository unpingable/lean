/-
  Surface Deformation Requires Coupling — scratch annex.

  Status: scratch proof-of-encodability, 2026-06-05 (v3). Not imported by
  `LeanProofs.lean`. Not part of any 1.0 surface. No paper anchor.
  No promotion path. NOT used as discharge for any doctrine.

  Filing category (per the doctrine map's Lean filing discipline):
    Fenced scratch proof-of-encodability. Pays its rent by forcing the
    architecture to confess which preservation obligations a lawful
    deformation owes. NOT category-1 (public/promoted), and conflating
    the two is the failure mode to watch for.

  Doctrine landings (per `working/tooltheory/surface-deformation-requires-coupling-candidate-2026-06-05.md`):

    * `CouplingWitness` is the `Deform`-family instance of the general
      bridge-witness shape; its obligation set is
      {temporal-bounding, type-fidelity}. See
      `working/bridge-obligation-lattice.md` for the lattice context.

    * The envelope theorem `deformation_difference_within_envelope` is the
      conservation law: no admissibility difference outside witnessed
      support. Derived as three contrapositives of the witness's invariance
      fields; not a new axiom.

    * `DeformationWellTyped` carries the type-fidelity obligation: the
      claimed deformation type must match the transform's behavior.
      `.convertTestimonyToConstraint` is intentionally not certifiable in
      this abstraction — coercive category change needs a richer model
      than one admissibility predicate, and asserting it under a Boolean
      flag is the v1 `requiresAdditionalWitness` failure mode this kernel
      explicitly evicted.

  Frontier (named not built):
    Composition. Step-wise lawful deformations do not silently compose
    into a lawful composite deformation. A composite witness must account
    for the gross ledger of behavioral flips, because cancellation is not
    the same as never having spent. Net is fakeable; gross isn't. See the
    candidate working note's § Frontier for the
    `SurfaceDeformationCompositionRequiresWitness` shape.

  Provenance:
    v1 / v2 / v3 evolved across 2026-06-05 in a multi-model review-and-
    repair cycle. v3 added the envelope theorem (derivable from the
    existing invariance fields). Landed in the corpus 2026-06-05 from
    `~/git/SurfaceDeformationRequiresCoupling.v3.lean`.

  Scope fence — what this file does NOT claim:
    * Not a runtime witness model. The Lean witness here is a dependent
      proof object; production witnesses (signed JSON, receipt rows,
      ledger entries) require a separate substrate bridge — see the
      candidate carrier sketch at `working/tooltheory/admissibility-related-work-map.md`
      § Substrate guidance § Candidate carrier sketch.
    * Not a model of policy supersession. `EffectiveSurface` is
      relational, not a selector — multiple effective candidates may
      coexist.
    * Not a model of composition. Single-step only; chained deformations
      live in the Frontier note.
    * Not part of any 1.0 module and not wired into `LeanProofs.lean`.
-/

/-
SurfaceDeformationRequiresCoupling.v3.lean

Events may deform admissibility surfaces only through typed coupling.
A surface deformation may exist as data, but a nontrivial alternate surface
cannot become an effective candidate unless a coupling witness authorizes the
event-surface-deformation triple, bounds it by scope and horizon, preserves
anti-retroactivity, and proves that the claimed deformation type matches the
transform's behavior.

This file is relational: it does not select a unique effective surface and does
not model supersession. It only states which candidate surfaces may be treated
as effective.

No-op deformations collapse behaviorally to the original surface and carry no
new authority. The triggering event cannot legitimate its past/self-at-time-t
claim through the deformation it allegedly caused.

Frontier: step-wise composition of deformations is intentionally absent. A
composite deformation needs a composite witness; otherwise horizons can be
laundered by chaining individually valid steps. A future composition artifact should
charge gross behavioral flips across the step ledger, not net endpoint difference;
cancellation is not the same as never having spent.
-/

namespace Admissibility.Backreaction

universe u

/-- A claim paired with the time at which it is evaluated or asserted. -/
structure TimedClaim (Claim : Type u) where
  claim : Claim
  timestamp : Nat

/-- An admissibility predicate over timed claims. -/
abbrev AdmissibilityPredicate (Claim : Type u) := TimedClaim Claim → Prop

/-- A surface determines admissibility for a class of claims. -/
structure Surface (Claim : Type u) where
  admit : AdmissibilityPredicate Claim

/-- Behavioral equivalence of surfaces. Avoids intensional equality of predicates. -/
def SurfaceEquiv {Claim : Type u} (left right : Surface Claim) : Prop :=
  ∀ claim : TimedClaim Claim, left.admit claim ↔ right.admit claim

/-- Admitted claims of `left` are a subset of admitted claims of `right`. -/
def SurfaceImplies {Claim : Type u} (left right : Surface Claim) : Prop :=
  ∀ claim : TimedClaim Claim, left.admit claim → right.admit claim

/-- Reflexivity of behavioral surface equivalence. -/
theorem surfaceEquiv_refl {Claim : Type u} (surface : Surface Claim) :
    SurfaceEquiv surface surface := by
  intro _claim
  rfl

/-- The coarse class of deformation being claimed. -/
inductive DeformationType where
  | expandAuthority
  | contractAuthority
  | quarantineSurface
  | raiseThreshold
  | lowerThreshold
  | expireStanding
  | convertTestimonyToConstraint
  | demoteConstraintToTestimony
  | closePath
  | openPath
  deriving DecidableEq, Repr

/-- Event kinds are intentionally opaque here; concrete systems refine them. -/
structure EventKind where
  name : String
  deriving DecidableEq, Repr

/-- An event that may be alleged to deform a surface. -/
structure Event where
  kind : EventKind
  timestamp : Nat
  deriving DecidableEq, Repr

/-- A deformation is just data: a claimed type plus a transform on surfaces. -/
structure SurfaceDeformation (Claim : Type u) where
  deformationType : DeformationType
  transform : Surface Claim → Surface Claim

/-- Applying a deformation computes a candidate surface. It grants no authority. -/
def applyDeformation {Claim : Type u}
    (surface : Surface Claim)
    (delta : SurfaceDeformation Claim) : Surface Claim :=
  delta.transform surface

/--
A well-typed deformation proves that the label on the deformation matches the
behavior of its transform, relative to the base surface.

Restrictive deformations may only remove admissibility. Permissive deformations
may only add admissibility. `convertTestimonyToConstraint` is intentionally not
certifiable in this abstraction: coercive category changes need a richer surface
model and an additional witness, not a Boolean flag.
-/
def DeformationWellTyped {Claim : Type u}
    (surface : Surface Claim)
    (delta : SurfaceDeformation Claim) : Prop :=
  let deformed := applyDeformation surface delta
  match delta.deformationType with
  | .expandAuthority => SurfaceImplies surface deformed
  | .lowerThreshold => SurfaceImplies surface deformed
  | .openPath => SurfaceImplies surface deformed
  | .contractAuthority => SurfaceImplies deformed surface
  | .quarantineSurface => SurfaceImplies deformed surface
  | .raiseThreshold => SurfaceImplies deformed surface
  | .expireStanding => SurfaceImplies deformed surface
  | .demoteConstraintToTestimony => SurfaceImplies deformed surface
  | .closePath => SurfaceImplies deformed surface
  | .convertTestimonyToConstraint => False

/--
A coupling witness authorizes a specific event/surface/deformation triple.

The invariants define the backreaction envelope:
* at or before the triggering event, the old and deformed surfaces agree;
* outside the named scope, they agree;
* after the named horizon, they agree;
* the claimed deformation type matches the transform behavior.

Only after the event, inside scope, and within horizon may the surfaces differ.
-/
structure CouplingWitness {Claim : Type u}
    (event : Event)
    (surface : Surface Claim)
    (delta : SurfaceDeformation Claim) where
  scope : TimedClaim Claim → Prop
  horizon : Nat
  withinHorizon : event.timestamp ≤ horizon
  wellTyped : DeformationWellTyped surface delta
  antiRetroactive : ∀ claim : TimedClaim Claim,
    claim.timestamp ≤ event.timestamp →
      (surface.admit claim ↔ (applyDeformation surface delta).admit claim)
  outsideScopeInvariant : ∀ claim : TimedClaim Claim,
    ¬ scope claim →
      (surface.admit claim ↔ (applyDeformation surface delta).admit claim)
  afterHorizonInvariant : ∀ claim : TimedClaim Claim,
    horizon < claim.timestamp →
      (surface.admit claim ↔ (applyDeformation surface delta).admit claim)

/-- No coupling witness exists for this specific event/surface/deformation triple. -/
abbrev NoCoupling {Claim : Type u}
    (event : Event)
    (surface : Surface Claim)
    (delta : SurfaceDeformation Claim) : Prop :=
  CouplingWitness event surface delta → False

/--
EffectiveDeformation answers whether this specific delta has deformation-authority.
A bare `SurfaceDeformation` has no authority; only coupling grants it.
-/
inductive EffectiveDeformation {Claim : Type u}
    (event : Event)
    (surface : Surface Claim)
    (delta : SurfaceDeformation Claim) : Prop where
  | byCoupling (w : CouplingWitness event surface delta) :
      EffectiveDeformation event surface delta

/-- A delta without a coupling witness has no deformation-authority. -/
theorem no_effective_deformation_without_coupling {Claim : Type u}
    (event : Event)
    (surface : Surface Claim)
    (delta : SurfaceDeformation Claim)
    (h_no_coupling : NoCoupling event surface delta) :
    ¬ EffectiveDeformation event surface delta := by
  intro h_eff
  cases h_eff with
  | byCoupling w => exact h_no_coupling w

/--
EffectiveSurface answers whether a candidate surface may be treated as in force.
This is relational, not a deterministic selector.

The original surface is always an effective candidate. A deformed surface is an
effective candidate only through a coupling witness. Candidate equality is
behavioral, not intensional.
-/
inductive EffectiveSurface {Claim : Type u}
    (event : Event)
    (surface : Surface Claim)
    (candidate : Surface Claim) : Prop where
  | original :
      SurfaceEquiv candidate surface →
        EffectiveSurface event surface candidate
  | deformed (delta : SurfaceDeformation Claim) :
      CouplingWitness event surface delta →
        SurfaceEquiv candidate (applyDeformation surface delta) →
          EffectiveSurface event surface candidate

/-- The original surface is always an effective candidate. -/
theorem original_surface_effective {Claim : Type u}
    (event : Event)
    (surface : Surface Claim) :
    EffectiveSurface event surface surface :=
  EffectiveSurface.original (surfaceEquiv_refl surface)

/--
Positive path: with a coupling witness, the deformed surface becomes an effective
candidate. This does not select a unique effective surface or supersede the old one.
-/
theorem deformed_surface_candidate_effective_by_coupling {Claim : Type u}
    (event : Event)
    (surface : Surface Claim)
    (delta : SurfaceDeformation Claim)
    (w : CouplingWitness event surface delta) :
    EffectiveSurface event surface (applyDeformation surface delta) :=
  EffectiveSurface.deformed delta w (surfaceEquiv_refl (applyDeformation surface delta))

/--
Without any coupling witness, every effective candidate collapses behaviorally to
the original surface. This is the operational refusal: the old surface remains in force.
-/
theorem no_alternate_effective_surface_without_coupling {Claim : Type u}
    (event : Event)
    (surface candidate : Surface Claim)
    (h_no_coupling : ∀ delta : SurfaceDeformation Claim,
      NoCoupling event surface delta)
    (h_eff : EffectiveSurface event surface candidate) :
    SurfaceEquiv candidate surface := by
  cases h_eff with
  | original h_equiv => exact h_equiv
  | deformed delta w _h_equiv =>
      exact False.elim ((h_no_coupling delta) w)

/--
A nontrivial deformed surface cannot be an effective candidate without some
coupling witness. No-op deformations are harmless: they collapse behaviorally to
the original surface and carry no new authority.
-/
theorem no_nontrivial_deformed_surface_without_coupling {Claim : Type u}
    (event : Event)
    (surface : Surface Claim)
    (delta : SurfaceDeformation Claim)
    (h_no_coupling : ∀ delta' : SurfaceDeformation Claim,
      NoCoupling event surface delta')
    (h_changed : ¬ SurfaceEquiv (applyDeformation surface delta) surface) :
    ¬ EffectiveSurface event surface (applyDeformation surface delta) := by
  intro h_eff
  cases h_eff with
  | original h_equiv =>
      exact h_changed h_equiv
  | deformed delta' w _h_equiv =>
      exact (h_no_coupling delta') w

/-- A valid coupling witnesses that its deformation label matches the transform. -/
theorem deformation_type_witnessed_by_valid_coupling {Claim : Type u}
    (event : Event)
    (surface : Surface Claim)
    (delta : SurfaceDeformation Claim)
    (w : CouplingWitness event surface delta) :
    DeformationWellTyped surface delta :=
  w.wellTyped

/--
The triggering event cannot legitimate its own claim at the event timestamp
through the deformation it allegedly caused. This does not block fresh assertions
inside the forward window; that requires a scope-specific no-forward-benefit rule.
-/
theorem no_self_legitimation_by_valid_coupling {Claim : Type u}
    (event : Event)
    (surface : Surface Claim)
    (delta : SurfaceDeformation Claim)
    (w : CouplingWitness event surface delta)
    (eventAsClaim : Event → TimedClaim Claim)
    (h_time : (eventAsClaim event).timestamp = event.timestamp)
    (h_not_old : ¬ surface.admit (eventAsClaim event))
    (h_new : (applyDeformation surface delta).admit (eventAsClaim event)) :
    False := by
  have h_le : (eventAsClaim event).timestamp ≤ event.timestamp :=
    Nat.le_of_eq h_time
  have h_same :=
    CouplingWitness.antiRetroactive w (eventAsClaim event) h_le
  exact h_not_old (h_same.mpr h_new)

/-- Valid coupling preserves admissibility outside the named scope. -/
theorem outside_scope_preserved_by_valid_coupling {Claim : Type u}
    (event : Event)
    (surface : Surface Claim)
    (delta : SurfaceDeformation Claim)
    (w : CouplingWitness event surface delta)
    (claim : TimedClaim Claim)
    (h_outside : ¬ w.scope claim) :
    surface.admit claim ↔ (applyDeformation surface delta).admit claim :=
  CouplingWitness.outsideScopeInvariant w claim h_outside

/-- Valid coupling preserves admissibility after the named horizon. -/
theorem after_horizon_preserved_by_valid_coupling {Claim : Type u}
    (event : Event)
    (surface : Surface Claim)
    (delta : SurfaceDeformation Claim)
    (w : CouplingWitness event surface delta)
    (claim : TimedClaim Claim)
    (h_after : w.horizon < claim.timestamp) :
    surface.admit claim ↔ (applyDeformation surface delta).admit claim :=
  CouplingWitness.afterHorizonInvariant w claim h_after

/-- Behavioral disagreement between two surfaces at a particular claim. -/
def SurfaceDiffers {Claim : Type u}
    (left right : Surface Claim)
    (claim : TimedClaim Claim) : Prop :=
  ¬ (left.admit claim ↔ right.admit claim)

/--
The live envelope in which a valid deformation may differ from the base surface:
after the triggering event, inside the named scope, and at or before horizon.
-/
def InDeformationEnvelope {Claim : Type u}
    (event : Event)
    {surface : Surface Claim}
    {delta : SurfaceDeformation Claim}
    (w : CouplingWitness event surface delta)
    (claim : TimedClaim Claim) : Prop :=
  event.timestamp < claim.timestamp ∧
    claim.timestamp ≤ w.horizon ∧
      w.scope claim

/--
Conservation law for lawful backreaction: if the old and deformed surfaces
disagree at a claim, that claim must lie inside the witnessed deformation
envelope. No admissibility difference exists outside witnessed support.
-/
theorem deformation_difference_within_envelope {Claim : Type u}
    (event : Event)
    (surface : Surface Claim)
    (delta : SurfaceDeformation Claim)
    (w : CouplingWitness event surface delta)
    (claim : TimedClaim Claim)
    (h_diff :
      SurfaceDiffers surface (applyDeformation surface delta) claim) :
    InDeformationEnvelope event w claim := by
  refine ⟨?_, ?_, ?_⟩
  · -- event.timestamp < claim.timestamp
    apply Nat.lt_of_not_ge
    intro h_le
    exact h_diff (CouplingWitness.antiRetroactive w claim h_le)
  · -- claim.timestamp ≤ w.horizon
    apply Nat.le_of_not_lt
    intro h_after
    exact h_diff (CouplingWitness.afterHorizonInvariant w claim h_after)
  · -- w.scope claim
    apply Classical.byContradiction
    intro h_outside
    exact h_diff (CouplingWitness.outsideScopeInvariant w claim h_outside)

/--
If the horizon equals the event timestamp, the coupling authorizes no behavioral
change. The live deformation window is `(event.timestamp, horizon]`.
-/
theorem coupling_at_horizon_is_noop {Claim : Type u}
    (event : Event)
    (surface : Surface Claim)
    (delta : SurfaceDeformation Claim)
    (w : CouplingWitness event surface delta)
    (h_horizon : w.horizon = event.timestamp) :
    SurfaceEquiv surface (applyDeformation surface delta) := by
  intro claim
  cases Nat.lt_or_ge event.timestamp claim.timestamp with
  | inl h_after_event =>
      have h_after_horizon : w.horizon < claim.timestamp := by
        rw [h_horizon]; exact h_after_event
      exact CouplingWitness.afterHorizonInvariant w claim h_after_horizon
  | inr h_before_or_at =>
      exact CouplingWitness.antiRetroactive w claim h_before_or_at

end Admissibility.Backreaction
