/-
  LeanProofs.CustodyIndexed.TemporalSurfaceAdapter -- real-module vocabulary adapter
  for the Temporal -> Surface bridge probe.

  Custody-Class: PUBLIC-SHIPPED
  Surface-Role: STABLE-SURFACE
  This stable adapter imports the public bounded-calculi evidence to express
  the `TemporalToSurfaceBridge` vocabulary without laundering meaning. It is
  reached through the exact `LeanProofs.CustodyIndexed` stable root.

  Adapter discipline:
    * The adapter maps only the temporal gate that has a real Surface atom today:
      `FreshAtUse` -> `SurfaceProjection.Atom.freshness`.
    * `LiveEpoch`, `ReplaySafeOperation`, and `VersionMatch` remain intentionally
      unmapped. They are not coerced into unrelated Surface atoms.
    * The bridge evidence is cell-local. It does not define transitive bridge
      composition, global admissibility, or boundary minting.
-/

import LeanProofs.BoundedCalculi.TemporalCustody
import LeanProofs.BoundedCalculi.SurfaceProjection

namespace LeanProofs.CustodyIndexed.TemporalSurfaceAdapter

open LeanProofs.BoundedCalculi

/-! ## Temporal gates and the explicit Surface adapter -/

/-- The four real TemporalCustody gate predicates, named as bridge vocabulary. -/
inductive TemporalGate where
  | freshAtUse
  | liveEpoch
  | replaySafe
  | versionMatch
  deriving DecidableEq

/-- Semantic interpretation of a temporal gate against the real Temporal module. -/
def TemporalGate.Holds
    (gate : TemporalGate)
    (env : TemporalCustody.Env)
    (action : TemporalCustody.Action) : Prop :=
  match gate with
  | .freshAtUse => TemporalCustody.FreshAtUse action
  | .liveEpoch => TemporalCustody.LiveEpoch env action
  | .replaySafe => TemporalCustody.ReplaySafeOperation env action
  | .versionMatch => TemporalCustody.VersionMatch env action

/-- The explicit, partial bridge vocabulary map into real Surface atoms.

    Absence is meaningful: an unmapped temporal gate cannot be demanded through
    this adapter. Future additions must name a Surface atom or explicit
    conversion and then re-check the affected negative theorems. -/
def TemporalGate.surfaceAtom : TemporalGate -> Option SurfaceProjection.Atom
  | .freshAtUse => some SurfaceProjection.Atom.freshness
  | .liveEpoch => none
  | .replaySafe => none
  | .versionMatch => none

def SurfaceRepresents
    (gate : TemporalGate) (atom : SurfaceProjection.Atom) : Prop :=
  gate.surfaceAtom = some atom

def DemandsGate (use : SurfaceProjection.Use) (gate : TemporalGate) : Prop :=
  ∃ atom : SurfaceProjection.Atom,
    SurfaceRepresents gate atom ∧ SurfaceProjection.Demands use atom

def RetainsGate
    (projection : SurfaceProjection.Projection) (gate : TemporalGate) : Prop :=
  ∃ atom : SurfaceProjection.Atom,
    SurfaceRepresents gate atom ∧ SurfaceProjection.Retains projection atom

def EstablishesMappedDemands
    (env : TemporalCustody.Env)
    (action : TemporalCustody.Action)
    (use : SurfaceProjection.Use) : Prop :=
  ∀ gate atom,
    SurfaceRepresents gate atom ->
    SurfaceProjection.Demands use atom ->
      gate.Holds env action

/-! ## Adapter sanity theorems -/

theorem temporally_valid_establishes_mapped_demands
    {env : TemporalCustody.Env}
    {action : TemporalCustody.Action}
    {use : SurfaceProjection.Use}
    (hvalid : TemporalCustody.TemporallyValid env action) :
    EstablishesMappedDemands env action use := by
  intro gate atom hrep _hdemand
  cases gate with
  | freshAtUse =>
      exact TemporalCustody.temporally_valid_requires_fresh_at_use hvalid
  | liveEpoch =>
      unfold SurfaceRepresents TemporalGate.surfaceAtom at hrep
      cases hrep
  | replaySafe =>
      unfold SurfaceRepresents TemporalGate.surfaceAtom at hrep
      cases hrep
  | versionMatch =>
      unfold SurfaceRepresents TemporalGate.surfaceAtom at hrep
      cases hrep

theorem unmapped_gate_not_demanded
    {use : SurfaceProjection.Use} {gate : TemporalGate}
    (hmap : gate.surfaceAtom = none) :
    ¬ DemandsGate use gate := by
  intro hdemand
  rcases hdemand with ⟨atom, hrep, _⟩
  unfold SurfaceRepresents at hrep
  rw [hmap] at hrep
  cases hrep

theorem live_epoch_not_surface_demanded
    (use : SurfaceProjection.Use) :
    ¬ DemandsGate use TemporalGate.liveEpoch :=
  unmapped_gate_not_demanded (use := use) (gate := TemporalGate.liveEpoch) rfl

theorem replay_safe_not_surface_demanded
    (use : SurfaceProjection.Use) :
    ¬ DemandsGate use TemporalGate.replaySafe :=
  unmapped_gate_not_demanded (use := use) (gate := TemporalGate.replaySafe) rfl

theorem version_match_not_surface_demanded
    (use : SurfaceProjection.Use) :
    ¬ DemandsGate use TemporalGate.versionMatch :=
  unmapped_gate_not_demanded (use := use) (gate := TemporalGate.versionMatch) rfl

theorem projected_use_demands_mapped_freshness :
    DemandsGate SurfaceProjection.Use.projectedUse TemporalGate.freshAtUse :=
  ⟨SurfaceProjection.Atom.freshness, rfl, rfl⟩

/-! ## Real-shape bridge evidence -/

structure BridgeEvidence
    (env : TemporalCustody.Env)
    (action : TemporalCustody.Action)
    (surface : SurfaceProjection.Surface)
    (projection : SurfaceProjection.Projection)
    (use : SurfaceProjection.Use) : Prop where
  temporal : TemporalCustody.TemporallyValid env action
  mappedTemporalDemands : EstablishesMappedDemands env action use
  sourceMatch : surface.source = projection.source
  retainedDemands :
    ∀ atom : SurfaceProjection.Atom,
      SurfaceProjection.Demands use atom ->
        SurfaceProjection.Retains projection atom

theorem bridge_evidence_of_temporally_valid_and_retained
    {env : TemporalCustody.Env}
    {action : TemporalCustody.Action}
    {surface : SurfaceProjection.Surface}
    {projection : SurfaceProjection.Projection}
    {use : SurfaceProjection.Use}
    (hvalid : TemporalCustody.TemporallyValid env action)
    (hsource : surface.source = projection.source)
    (hretained :
      ∀ atom : SurfaceProjection.Atom,
        SurfaceProjection.Demands use atom ->
          SurfaceProjection.Retains projection atom) :
    BridgeEvidence env action surface projection use where
  temporal := hvalid
  mappedTemporalDemands := temporally_valid_establishes_mapped_demands hvalid
  sourceMatch := hsource
  retainedDemands := hretained

theorem bridge_evidence_authorizes_surface
    {env : TemporalCustody.Env}
    {action : TemporalCustody.Action}
    {surface : SurfaceProjection.Surface}
    {projection : SurfaceProjection.Projection}
    {use : SurfaceProjection.Use}
    (hbridge : BridgeEvidence env action surface projection use) :
    SurfaceProjection.ProjectionAuthorized surface projection use :=
  SurfaceProjection.retained_witnesses_authorize
    hbridge.sourceMatch hbridge.retainedDemands

theorem temporal_surface_bridge_authorizes
    {env : TemporalCustody.Env}
    {action : TemporalCustody.Action}
    {surface : SurfaceProjection.Surface}
    {projection : SurfaceProjection.Projection}
    {use : SurfaceProjection.Use}
    (hvalid : TemporalCustody.TemporallyValid env action)
    (hsource : surface.source = projection.source)
    (hretained :
      ∀ atom : SurfaceProjection.Atom,
        SurfaceProjection.Demands use atom ->
          SurfaceProjection.Retains projection atom) :
    SurfaceProjection.ProjectionAuthorized surface projection use :=
  bridge_evidence_authorizes_surface
    (bridge_evidence_of_temporally_valid_and_retained hvalid hsource hretained)

/-! ## Retention wall on the mapped freshness cell -/

def projectedSurface : SurfaceProjection.Surface where
  source := SurfaceProjection.Source.projection

def droppedFreshnessRetained : SurfaceProjection.Atom -> Bool
  | .nonAmplification => true
  | .typeFidelity => true
  | _ => false

def droppedFreshnessProjection : SurfaceProjection.Projection where
  source := SurfaceProjection.Source.projection
  retained := droppedFreshnessRetained

theorem dropped_freshness_projection_retains_no_freshness :
    ¬ SurfaceProjection.Retains
        droppedFreshnessProjection SurfaceProjection.Atom.freshness := by
  intro h
  unfold SurfaceProjection.Retains droppedFreshnessProjection
    droppedFreshnessRetained at h
  exact Bool.noConfusion h

/-- Real-shape retention wall: even with a real temporally-valid action, the
    projected use is not authorized when the mapped freshness atom is dropped. -/
theorem temporal_validity_does_not_authorize_dropped_mapped_freshness :
    TemporalCustody.TemporallyValid
        TemporalCustody.permissiveEnv TemporalCustody.fullyCheckedAction ∧
      ¬ SurfaceProjection.ProjectionAuthorized
          projectedSurface
          droppedFreshnessProjection
          SurfaceProjection.Use.projectedUse := by
  constructor
  · exact TemporalCustody.fully_checked_action_temporally_valid
  · intro hauth
    have hretained :
        SurfaceProjection.Retains
          droppedFreshnessProjection SurfaceProjection.Atom.freshness :=
      SurfaceProjection.authorized_projection_retains_every_demanded_atom
        hauth SurfaceProjection.Atom.freshness rfl
    exact dropped_freshness_projection_retains_no_freshness hretained

end LeanProofs.CustodyIndexed.TemporalSurfaceAdapter
