# Worked example — Temporal → Surface vocabulary alignment

*Alignment log, not a roadmap.* Snapshot readout of the vocabulary boundary
between the L2 bridge scratch and the real bounded-calculi modules, produced
during the codex L2 pass (2026-07-01). The forward plan and as-built status
ledger live in `docs/ROADMAP-bounded-calculi.md` (§11); this file archives the
detailed mapping table that drove the freshness-only adapter decision.

> **v13 path correction:** the real adapter now lives at
> `LeanProofs/CustodyIndexed/TemporalSurfaceAdapter.lean`, and the Bounded
> Calculi modules are public shipped. The self-contained
> `TemporalToSurfaceBridge.lean` surrogate was superseded and deleted; its
> exact source remains in v12/Git history. This document intentionally retains
> the 2026-07-01 comparison as a historical design record.

## Temporal To Surface Vocabulary Alignment

Files read for this alignment:

- historical v12 `LeanProofs/Scratch/TemporalToSurfaceBridge.lean`
- `LeanProofs/BoundedCalculi/TemporalCustody.lean`
- `LeanProofs/BoundedCalculi/SurfaceProjection.lean`

Adapter file:

- `LeanProofs/CustodyIndexed/TemporalSurfaceAdapter.lean`

### Historical surrogate vocabulary

The scratch bridge uses:

- Temporal atoms: `freshAtUse`, `liveEpoch`, `versionMatch`, `replaySafe`
- Demanded surface atoms: `Use.demanded : List TemporalAtom`
- Retained/projection atoms: `Projection.retained : List TemporalAtom`
- Bridge witness/constructor: `ProjectionAuthorized.bridge`
- Failed-cut witnesses: a demanded atom that is established but dropped from retention, and a demanded atom retained but not established
- Non-transfer target: local scratch `MayMint`, guarded by `mintEdge`

### Real Temporal Vocabulary

`TemporalCustody` has predicate gates over `Env` and `Action`:

- `FreshAtUse`
- `LiveEpoch`
- `ReplaySafeOperation`
- `VersionMatch`
- `TemporallyValid`

Positive path:

- `checked_action_temporally_valid`
- `fully_checked_action_temporally_valid`

Gate projection and blocker theorem shapes:

- `temporally_valid_requires_fresh_at_use`
- `temporally_valid_requires_live_epoch`
- `temporally_valid_requires_replay_safe_operation`
- `temporally_valid_requires_version_match`
- `not_fresh_at_use_blocks_temporal_validity`
- `dead_epoch_blocks_temporal_validity`
- `replay_unsafe_blocks_temporal_validity`
- `version_mismatch_blocks_temporal_validity`
- `any_missing_required_component_blocks_temporal_validity`
- `temporally_valid_iff_all_use_time_gates`
- `citation_and_signature_do_not_discharge_missing_use_time_component`

Specimen/non-collapse examples include:

- `citation_time_validity_does_not_imply_execution_admissibility`
- `fresh_signed_artifact_does_not_imply_live_epoch`
- `fresh_observation_does_not_imply_version_valid_mutation`

### Real Surface Vocabulary

`SurfaceProjection` has finite surface atoms and uses:

- Demanded atoms: `Demands : Use -> Atom -> Prop`, backed by `demandsB`
- Retained atoms: `Retains : Projection -> Atom -> Prop`
- Explicit conversion: `Conversion : Source -> Use -> Atom -> Atom -> Prop`; currently identity only
- Supply relation: `CanSupply`, by retained atom or explicit conversion
- Authorization judgment: `ProjectionAuthorized surface projection use`

Authorization supplies/retains demanded atoms:

- `projection_authorized_supplies_every_demanded_atom`
- `can_supply_by_retention_or_explicit_conversion`
- `can_supply_requires_retained_atom`
- `authorized_projection_retains_every_demanded_atom`
- `authorized_projection_supplies_every_demanded_atom_by_retention_or_conversion`
- `demanded_atom_without_retention_or_conversion_blocks_authorization`

Log/projection non-collapse theorem shapes:

- `collapsed_surface_without_discriminator_cannot_authorize_cause_specific`
- `log_emission_does_not_prove_truth`
- `log_emission_does_not_prove_authorization`
- `lift_cannot_silently_discharge_projection_freshness`
- `lift_cannot_silently_discharge_projection_nonAmplification`

### Mapping Table

| Surrogate term | Real Temporal term | Real Surface term | Status |
|---|---|---|---|
| `TemporalAtom.freshAtUse` | `FreshAtUse a` | `Atom.freshness` for `Use.projectedUse` | exact match via scratch adapter |
| `TemporalAtom.liveEpoch` | `LiveEpoch env a` | no current atom | deliberately unmapped by adapter |
| `TemporalAtom.replaySafe` | `ReplaySafeOperation env a` | no current atom | deliberately unmapped by adapter |
| `TemporalAtom.versionMatch` | `VersionMatch env a` | no current atom | deliberately unmapped by adapter |
| `Source.established : List TemporalAtom` | conjunction/projections from `TemporallyValid env a` | no direct source-established field | close but needs adapter |
| `Use.demanded : List TemporalAtom` | no direct demand structure | `Demands use atom` over `SurfaceProjection.Atom` | close but needs adapter |
| `Projection.retained : List TemporalAtom` | no direct retention structure | `Retains projection atom` | close but needs adapter |
| `ProjectionAuthorized.bridge` | `TemporallyValid.checked` evidence can supply temporal gates | `ProjectionAuthorized.byWitnesses` with `CanSupply` for demanded atoms | close but needs adapter |
| `bridge_authorizes` | `checked_action_temporally_valid` | `retained_witnesses_authorize` | close but needs adapter |
| `projection_authorization_requires_bridge_evidence` | temporal gate projection theorems | `projection_authorized_supplies_every_demanded_atom`; `authorized_projection_retains_every_demanded_atom` | close but needs adapter |
| dropped-retention failed cut | source can satisfy `VersionMatch env a` | `demanded_atom_without_retention_or_conversion_blocks_authorization` | close but needs adapter |
| retained-but-unestablished failed cut | `any_missing_required_component_blocks_temporal_validity` blocks source validity | no surface theorem about temporal establishment | close but needs adapter |
| scratch `MayMint` / `mintEdge` | no target | no target in `SurfaceProjection`; real target is likely `BoundaryArtifact.MayMint` | surrogate-only |
| transitive bridge composition | no default composition | no default composition | should not map |
| global `Admissible` conclusion | no term | no term | should not map |

## Adapter Definitions

`LeanProofs/CustodyIndexed/TemporalSurfaceAdapter.lean` defines the explicit adapter surface:

- `TemporalGate`
- `TemporalGate.Holds`
- `TemporalGate.surfaceAtom`
- `SurfaceRepresents`
- `DemandsGate`
- `RetainsGate`
- `EstablishesMappedDemands`
- `BridgeEvidence`

The adapter maps only:

- `TemporalGate.freshAtUse` to `SurfaceProjection.Atom.freshness`

The adapter deliberately does not map:

- `TemporalGate.liveEpoch`
- `TemporalGate.replaySafe`
- `TemporalGate.versionMatch`

The no-laundering guards are:

- `live_epoch_not_surface_demanded`
- `replay_safe_not_surface_demanded`
- `version_match_not_surface_demanded`

The real-shape bridge pressure is:

- `temporal_surface_bridge_authorizes`
- `temporal_validity_does_not_authorize_dropped_mapped_freshness`

## Alignment Conclusion

Green, scoped: a real-shape wiring probe is plausible with the small scratch adapter in
`LeanProofs/CustodyIndexed/TemporalSurfaceAdapter.lean`.

The plausible core is:

- Real `TemporalCustody.TemporallyValid env a` exposes gates through projection theorems.
- Real `SurfaceProjection.ProjectionAuthorized surface projection use` already requires every demanded atom to be supplied by retention or explicit conversion.
- The dropped-retention wall has a real Surface theorem shape in `demanded_atom_without_retention_or_conversion_blocks_authorization`.

The remaining boundary is vocabulary shape, not proof strength. The historical
surrogate atoms used one local enum for both temporal establishment and surface
demand/retention. Real modules split those roles:

- Temporal gates are predicates over `Env` and `Action`.
- Surface demanded/retained atoms are members of `SurfaceProjection.Atom`.
- Only `freshness` currently has an obvious surface atom; `liveEpoch`, `replaySafe`, and `versionMatch` have no direct real Surface atoms and are intentionally unmapped.

Any further real-shape probe must use the adapter as explicit bridge evidence. Extending the map beyond freshness requires a future Surface vocabulary or explicit conversion choice, plus re-checking the affected negative theorems.

*Slice order and forbidden-moves discipline are not restated here — see
`docs/ROADMAP-bounded-calculi.md` §9–§11.*
