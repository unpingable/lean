/-
  LeanProofs.Scratch.TemporalToSurfaceBridgeWiring -- real-shape wiring probe
  for the Temporal -> Surface bridge.

  Custody-Class: SCRATCH. Unpromoted, compile-is-contact only, not authority-
  bearing. This module is not imported by `LeanProofs.lean`,
  `LeanProofs.BoundedCalculi`, or any promoted kernel.

  This does NOT replace `TemporalToSurfaceBridge.lean`; it is a second probe
  that imports the real bounded-calculi vocabularies and the scratch adapter
  that makes the Temporal gate -> Surface atom mapping explicit.

  Global-admissibility discipline: this file does not define an `Admissible`
  judgment. The non-transfer target for "global admissibility" is expressed as
  an arbitrary external claim that must already be established elsewhere.
-/

import LeanProofs.BoundedCalculi.TemporalCustody
import LeanProofs.BoundedCalculi.SurfaceProjection
import LeanProofs.Scratch.TemporalSurfaceAdapter
import LeanProofs.BoundedCalculi.BoundaryArtifact
import LeanProofs.BoundedCalculi.SafetyPreservation
import LeanProofs.BoundedCalculi.ObligationResidue

namespace LeanProofs.Scratch.TemporalToSurfaceBridgeWiring

open LeanProofs.BoundedCalculi
/-! ## Real Surface supply: retained or explicitly converted -/

theorem can_supply_of_retention_or_explicit_conversion
    {projection : SurfaceProjection.Projection}
    {use : SurfaceProjection.Use}
    {atom : SurfaceProjection.Atom}
    (h : SurfaceProjection.SuppliedByRetentionOrConversion projection use atom) :
    SurfaceProjection.CanSupply projection use atom := by
  cases h with
  | inl hretained =>
      exact SurfaceProjection.CanSupply.retained hretained
  | inr hconverted =>
      rcases hconverted with ⟨provided, hretained, hconversion⟩
      exact SurfaceProjection.CanSupply.converted hretained hconversion

structure TemporalSurfaceBridgeEvidence
    (env : TemporalCustody.Env)
    (action : TemporalCustody.Action)
    (surface : SurfaceProjection.Surface)
    (projection : SurfaceProjection.Projection)
    (use : SurfaceProjection.Use) : Prop where
  temporal : TemporalCustody.TemporallyValid env action
  mappedTemporalDemands : LeanProofs.Scratch.TemporalSurfaceAdapter.EstablishesMappedDemands env action use
  sourceMatch : surface.source = projection.source
  suppliedDemands :
    ∀ atom : SurfaceProjection.Atom,
      SurfaceProjection.Demands use atom ->
        SurfaceProjection.SuppliedByRetentionOrConversion projection use atom

/-- Positive bridge: once the temporal side is valid and every real Surface demand
    is supplied by retention or explicit conversion, the real Surface authorization
    constructor fires. -/
theorem positive_bridge_authorizes_when_retained_or_converted
    {env : TemporalCustody.Env}
    {action : TemporalCustody.Action}
    {surface : SurfaceProjection.Surface}
    {projection : SurfaceProjection.Projection}
    {use : SurfaceProjection.Use}
    (hbridge :
      TemporalSurfaceBridgeEvidence env action surface projection use) :
    SurfaceProjection.ProjectionAuthorized surface projection use :=
  SurfaceProjection.ProjectionAuthorized.byWitnesses
    hbridge.sourceMatch
    (fun atom hdemand =>
      can_supply_of_retention_or_explicit_conversion
        (hbridge.suppliedDemands atom hdemand))

theorem positive_bridge_authorization_supplies_demands_by_real_rules
    {env : TemporalCustody.Env}
    {action : TemporalCustody.Action}
    {surface : SurfaceProjection.Surface}
    {projection : SurfaceProjection.Projection}
    {use : SurfaceProjection.Use}
    (hbridge :
      TemporalSurfaceBridgeEvidence env action surface projection use) :
    ∀ atom : SurfaceProjection.Atom,
      SurfaceProjection.Demands use atom ->
        SurfaceProjection.SuppliedByRetentionOrConversion projection use atom :=
  SurfaceProjection.authorized_projection_supplies_every_demanded_atom_by_retention_or_conversion
    (positive_bridge_authorizes_when_retained_or_converted hbridge)

/-! ## Concrete positive path over the real projected-use surface -/

def projectedSurface : SurfaceProjection.Surface where
  source := SurfaceProjection.Source.projection

def retainedProjectedUseAtoms : SurfaceProjection.Atom -> Bool
  | .freshness => true
  | .nonAmplification => true
  | .typeFidelity => true
  | _ => false

def retainedProjectedUseProjection : SurfaceProjection.Projection where
  source := SurfaceProjection.Source.projection
  retained := retainedProjectedUseAtoms

theorem projected_use_demands_are_retained :
    ∀ atom : SurfaceProjection.Atom,
      SurfaceProjection.Demands SurfaceProjection.Use.projectedUse atom ->
        SurfaceProjection.Retains retainedProjectedUseProjection atom := by
  intro atom hdemand
  cases atom <;>
    simp [SurfaceProjection.Demands, SurfaceProjection.demandsB,
      SurfaceProjection.Retains, retainedProjectedUseProjection,
      retainedProjectedUseAtoms] at hdemand ⊢

theorem projected_use_demands_supplied_by_real_rules :
    ∀ atom : SurfaceProjection.Atom,
      SurfaceProjection.Demands SurfaceProjection.Use.projectedUse atom ->
        SurfaceProjection.SuppliedByRetentionOrConversion
          retainedProjectedUseProjection SurfaceProjection.Use.projectedUse atom := by
  intro atom hdemand
  exact Or.inl (projected_use_demands_are_retained atom hdemand)

theorem concrete_temporal_surface_bridge_evidence :
    TemporalSurfaceBridgeEvidence
      TemporalCustody.permissiveEnv
      TemporalCustody.fullyCheckedAction
      projectedSurface
      retainedProjectedUseProjection
      SurfaceProjection.Use.projectedUse where
  temporal := TemporalCustody.fully_checked_action_temporally_valid
  mappedTemporalDemands :=
    LeanProofs.Scratch.TemporalSurfaceAdapter.temporally_valid_establishes_mapped_demands
      TemporalCustody.fully_checked_action_temporally_valid
  sourceMatch := rfl
  suppliedDemands := projected_use_demands_supplied_by_real_rules

theorem concrete_positive_bridge_authorizes_projected_use :
    SurfaceProjection.ProjectionAuthorized
      projectedSurface
      retainedProjectedUseProjection
      SurfaceProjection.Use.projectedUse :=
  positive_bridge_authorizes_when_retained_or_converted
    concrete_temporal_surface_bridge_evidence

/-! ## Failed cut: temporal validity alone does not authorize dropped freshness -/

theorem dropped_projection_drops_mapped_freshness :
    ¬ LeanProofs.Scratch.TemporalSurfaceAdapter.RetainsGate
        LeanProofs.Scratch.TemporalSurfaceAdapter.droppedFreshnessProjection LeanProofs.Scratch.TemporalSurfaceAdapter.TemporalGate.freshAtUse := by
  intro h
  rcases h with ⟨atom, hrep, hretained⟩
  unfold LeanProofs.Scratch.TemporalSurfaceAdapter.SurfaceRepresents LeanProofs.Scratch.TemporalSurfaceAdapter.TemporalGate.surfaceAtom at hrep
  cases hrep
  exact LeanProofs.Scratch.TemporalSurfaceAdapter.dropped_freshness_projection_retains_no_freshness hretained

theorem temporally_valid_does_not_authorize_when_mapped_freshness_dropped :
    ∃ (env : TemporalCustody.Env)
      (action : TemporalCustody.Action)
      (surface : SurfaceProjection.Surface)
      (projection : SurfaceProjection.Projection),
      TemporalCustody.TemporallyValid env action ∧
      LeanProofs.Scratch.TemporalSurfaceAdapter.DemandsGate SurfaceProjection.Use.projectedUse LeanProofs.Scratch.TemporalSurfaceAdapter.TemporalGate.freshAtUse ∧
      ¬ LeanProofs.Scratch.TemporalSurfaceAdapter.RetainsGate projection LeanProofs.Scratch.TemporalSurfaceAdapter.TemporalGate.freshAtUse ∧
      ¬ SurfaceProjection.ProjectionAuthorized
          surface projection SurfaceProjection.Use.projectedUse := by
  refine ⟨TemporalCustody.permissiveEnv,
    TemporalCustody.fullyCheckedAction,
    LeanProofs.Scratch.TemporalSurfaceAdapter.projectedSurface,
    LeanProofs.Scratch.TemporalSurfaceAdapter.droppedFreshnessProjection,
    ?_, ?_, ?_, ?_⟩
  · exact TemporalCustody.fully_checked_action_temporally_valid
  · exact LeanProofs.Scratch.TemporalSurfaceAdapter.projected_use_demands_mapped_freshness
  · exact dropped_projection_drops_mapped_freshness
  · exact LeanProofs.Scratch.TemporalSurfaceAdapter.temporal_validity_does_not_authorize_dropped_mapped_freshness.2

/-! ## Non-transfer targets: boundary, safety, obligation, external global claim -/

inductive DemoDomain where
  | internal
  | external

inductive DemoFailure where
  | escaped

def sealedBoundary : BoundaryArtifact.Boundary DemoDomain where
  authorized := fun _ _ => false

def escapedExposure : BoundaryArtifact.Exposure DemoDomain DemoFailure where
  origin := DemoDomain.internal
  target := DemoDomain.external
  failure := DemoFailure.escaped

theorem sealed_exposure_not_mintable :
    ¬ BoundaryArtifact.MayMint
        sealedBoundary
        (BoundaryArtifact.Artifact.exposure escapedExposure) := by
  intro h
  cases h with
  | exposure hauth =>
      simp [sealedBoundary] at hauth

theorem temporal_surface_bridge_does_not_imply_boundary_minting :
    SurfaceProjection.ProjectionAuthorized
      projectedSurface
      retainedProjectedUseProjection
      SurfaceProjection.Use.projectedUse ∧
    ¬ BoundaryArtifact.MayMint
        sealedBoundary
        (BoundaryArtifact.Artifact.exposure escapedExposure) :=
  ⟨concrete_positive_bridge_authorizes_projected_use,
    sealed_exposure_not_mintable⟩

theorem temporal_surface_bridge_does_not_imply_safety_preservation :
    SurfaceProjection.ProjectionAuthorized
      projectedSurface
      retainedProjectedUseProjection
      SurfaceProjection.Use.projectedUse ∧
    ¬ SafetyPreservation.SafeAllowed
        SafetyPreservation.toyEnv
        SafetyPreservation.ToyState.clean
        SafetyPreservation.ToyActor.operator
        SafetyPreservation.ToyAction.damage :=
  ⟨concrete_positive_bridge_authorizes_projected_use,
    SafetyPreservation.authorized_damage_step_cannot_be_safeAllowed.2⟩

inductive DemoClaim where
  | projectedUse

inductive DemoObligation where
  | live
  | unrelated
  deriving DecidableEq

def unrelatedReceipt :
    ObligationResidue.AccountingReceipt DemoClaim DemoObligation where
  claim := DemoClaim.projectedUse
  obligation := DemoObligation.unrelated

theorem unrelated_receipt_does_not_account_live_obligation :
    ¬ ObligationResidue.ReceiptAccounts
        unrelatedReceipt DemoObligation.live :=
  ObligationResidue.receipt_cannot_account_unrelated_obligation
    unrelatedReceipt DemoObligation.live (by decide)

theorem temporal_surface_bridge_does_not_discharge_obligation :
    SurfaceProjection.ProjectionAuthorized
      projectedSurface
      retainedProjectedUseProjection
      SurfaceProjection.Use.projectedUse ∧
    ¬ ObligationResidue.ReceiptAccounts
        unrelatedReceipt DemoObligation.live :=
  ⟨concrete_positive_bridge_authorizes_projected_use,
    unrelated_receipt_does_not_account_live_obligation⟩

/-- This is the legal replacement for a forbidden master `Admissible` target:
    the bridge does not discharge an arbitrary external/global claim that is
    independently false. Consumers must supply their own claim and proof; this
    file does not mint a global admissibility judgment. -/
theorem temporal_surface_bridge_does_not_imply_external_global_claim
    {ExternalGlobalClaim : Prop}
    (hnotGlobal : ¬ ExternalGlobalClaim) :
    SurfaceProjection.ProjectionAuthorized
      projectedSurface
      retainedProjectedUseProjection
      SurfaceProjection.Use.projectedUse ∧
    ¬ ExternalGlobalClaim :=
  ⟨concrete_positive_bridge_authorizes_projected_use, hnotGlobal⟩

theorem temporal_surface_bridge_nontransfer_bundle
    {ExternalGlobalClaim : Prop}
    (hnotGlobal : ¬ ExternalGlobalClaim) :
    SurfaceProjection.ProjectionAuthorized
      projectedSurface
      retainedProjectedUseProjection
      SurfaceProjection.Use.projectedUse ∧
    ¬ BoundaryArtifact.MayMint
        sealedBoundary
        (BoundaryArtifact.Artifact.exposure escapedExposure) ∧
    ¬ SafetyPreservation.SafeAllowed
        SafetyPreservation.toyEnv
        SafetyPreservation.ToyState.clean
        SafetyPreservation.ToyActor.operator
        SafetyPreservation.ToyAction.damage ∧
    ¬ ObligationResidue.ReceiptAccounts
        unrelatedReceipt DemoObligation.live ∧
    ¬ ExternalGlobalClaim :=
  ⟨concrete_positive_bridge_authorizes_projected_use,
    sealed_exposure_not_mintable,
    SafetyPreservation.authorized_damage_step_cannot_be_safeAllowed.2,
    unrelated_receipt_does_not_account_live_obligation,
    hnotGlobal⟩

/-! ## Reverse cut + bidirectional independence (Run C strengthening, 2026-07-01)

    The codex audit of the positive path found temporal validity was carried but
    unused: `positive_bridge_authorizes_when_retained_or_converted` authorizes from
    Surface retention alone. Rather than coerce temporal into the current Surface
    vocabulary (which would extend the ANNEX module and open new-atom design), we make
    the DECOUPLING explicit: neither judgment implies the other, and the two are
    coupled ONLY by the explicit `TemporalSurfaceBridgeEvidence` (which demands both a
    temporally-valid action AND supplied Surface demands). This is the honest "no
    cross-calculus cut without an explicit bridge" at the current vocabulary. -/

/-- Reverse cut: real Surface projection authorization does not imply temporal
    validity. Witnessed by a fully-retained projection (authorized) against a
    stale-at-execution action (not fresh at use -> not temporally valid). -/
theorem surface_authorized_does_not_imply_temporally_valid :
    SurfaceProjection.ProjectionAuthorized
        projectedSurface retainedProjectedUseProjection
        SurfaceProjection.Use.projectedUse ∧
      ¬ TemporalCustody.TemporallyValid
          TemporalCustody.permissiveEnv TemporalCustody.staleAtExecutionAction :=
  ⟨concrete_positive_bridge_authorizes_projected_use,
    TemporalCustody.staleAtExecution_not_temporally_valid⟩

/-- Bidirectional independence capstone: neither temporal validity nor Surface
    projection authorization implies the other, refuting any UNCONDITIONAL / free
    cross-calculus cut in either direction.

    Scope (precise, per adversarial audit 2026-07-01): this is *product* orthogonality
    at the current vocabulary — each existential witness pairs an authorized
    `(surface, projection)` with an *independently chosen* `(env, action)`. It does NOT
    assert semantic independence over a single shared bridged configuration; indeed
    `ProjectionAuthorized` does not reference an `env`/`action`, so a "same-config"
    coupling is not even expressible here. The only thing that couples the two calculi
    is explicit `TemporalSurfaceBridgeEvidence` (which demands both a temporally-valid
    action and supplied Surface demands). No master `Admissible`. -/
theorem temporal_surface_mutual_nonimplication :
    (∃ (env : TemporalCustody.Env) (action : TemporalCustody.Action)
        (surface : SurfaceProjection.Surface)
        (projection : SurfaceProjection.Projection),
        TemporalCustody.TemporallyValid env action ∧
        ¬ SurfaceProjection.ProjectionAuthorized
            surface projection SurfaceProjection.Use.projectedUse) ∧
    (∃ (surface : SurfaceProjection.Surface)
        (projection : SurfaceProjection.Projection)
        (env : TemporalCustody.Env) (action : TemporalCustody.Action),
        SurfaceProjection.ProjectionAuthorized
            surface projection SurfaceProjection.Use.projectedUse ∧
        ¬ TemporalCustody.TemporallyValid env action) :=
  ⟨⟨TemporalCustody.permissiveEnv, TemporalCustody.fullyCheckedAction,
     LeanProofs.Scratch.TemporalSurfaceAdapter.projectedSurface,
     LeanProofs.Scratch.TemporalSurfaceAdapter.droppedFreshnessProjection,
     LeanProofs.Scratch.TemporalSurfaceAdapter.temporal_validity_does_not_authorize_dropped_mapped_freshness⟩,
   ⟨projectedSurface, retainedProjectedUseProjection,
     TemporalCustody.permissiveEnv, TemporalCustody.staleAtExecutionAction,
     concrete_positive_bridge_authorizes_projected_use,
     TemporalCustody.staleAtExecution_not_temporally_valid⟩⟩

end LeanProofs.Scratch.TemporalToSurfaceBridgeWiring
