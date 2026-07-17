# Semantic Wiring Audit

> **Policy/status update (2026-07-14):** this dated audit contains historical
> consumer-gated recommendations that are no longer operative. Formalization
> may lead adoption; consumers are correspondence targets, not permission to
> build. In particular, `firstViolation_none_iff_lawful` landed in
> `DeferredWitness.lean` on 2026-07-09. Custody and public promotion remain
> separate operator decisions.

> **v13 custody update:** ANNEX/Scratch/candidate paths and recommendations in
> this report are historical. Finished work is now stable API or public
> evidence; live incubation is in skunkworks; superseded fossils remain in
> v12/Git history. Current state:
> [`docs/V13-RELEASE-LEDGER.md`](docs/V13-RELEASE-LEDGER.md).

This is a semantic wiring audit, not an inventory audit. It asks what already
exists in the repo that should be connected, factored, generalized, exercised,
or made legible as a dependency, without promoting scratch into doctrine.

Core reading rules used here:

- Compilation is contact, not truth.
- Scratch may inform wiring, but scratch may not testify.
- `True` placeholders, marker theorems, axioms, examples, and import reachability
  do not count as substantive claims.
- A proposed edge is listed only when its source object, target object or missing
  interface, exact Lean definitions/theorems, semantic dependency, stranding
  reason, and custody class can be named.

## Preflight

Required commands were run before writing this report.

| Command | Result |
| --- | --- |
| `git status --short` | Existing dirty state: `M LeanProofs/Scratch/QuorumCustody.lean`, `?? AUDIT_LEAN_REPO.md` |
| `lake build` | Passed |
| `lake build Witnessed` | Passed |
| `bash scripts/check-witnessed-footprint.sh` | Passed after sandbox escalation: 10 ratified Witnessed receipts, Mathlib-free, expected axiom footprint |
| `bash scripts/check-custody-classes.sh` | Failed only on README count drift: README states ANNEX = 25 and total `.lean` files = 51; live tally is ANNEX = 27 and total = 53 |

The custody count drift is background radiation for this audit. It should be
fixed in a separate prose-reconciliation pass, not in the semantic wiring pass.

## Concept clusters

### Admissibility kernels

Role: the stable public kernel surface for local admissibility, authorization,
state mutation, corrective monotonicity, freshness, surface authorization, and
witness invariance.

- Defining files:
  - `LeanProofs/Admissibility/Authority.lean`
  - `LeanProofs/Admissibility/StateTransition.lean`
  - `LeanProofs/Admissibility/Derivation.lean`
  - `LeanProofs/Admissibility/Execution.lean`
  - `LeanProofs/Admissibility/Corrective.lean`
  - `LeanProofs/Admissibility/Freshness.lean`
  - `LeanProofs/Admissibility/SurfaceAuthorization.lean`
  - `LeanProofs/Admissibility/WitnessInvariance.lean`
  - `LeanProofs/Admissibility/AdmissibilityKernels.lean`
- Supporting objects:
  - `Authority.authorityVerdict`
  - `Authority.authorized_iff_all_green`
  - `Authority.no_basis_never_authorized`
  - `Authority.advisory_basis_never_authorized`
  - `Authority.conflicting_precedence_never_authorized`
  - `StateTransition.StepAllowed`
  - `StateTransition.executeIfAllowed`
  - `Derivation.decideAuthority`
  - `Derivation.decide_authorized_requires_all_green`
  - `Derivation.revoked_basis_never_authorized`
  - `Execution.AuthorizedStep`
  - `Execution.revoked_basis_cannot_be_authorized_step`
  - `Corrective.WeaklyLessPermissive`
  - `Corrective.CorrectiveMonotone`
  - `Freshness.Fresh`
  - `Freshness.expired_not_fresh`
  - `Freshness.not_yet_valid_not_fresh`
  - `Freshness.divergence_excessive_not_fresh`
  - `SurfaceAuthorization.authorize`
  - `SurfaceAuthorization.collapsed_surface_denies_cause_specific_without_breaker`
  - `WitnessInvariance.Encapsulated`
  - `WitnessInvariance.moves_implies_not_encapsulated`
- Example/specimen files:
  - `LeanProofs/Admissibility/Examples.lean`
  - named specimens include `specimen_valid_authorized_mutation`,
    `specimen_stale_evidence_refusal`, `specimen_self_cert_denial`,
    `specimen_receipt_no_authority_upgrade`, and
    `specimen_open_finding_accounted`
- Docs/registers:
  - `README.md`
  - `LeanProofs/Admissibility/README.md`
  - `WHAT-THIS-PROVES.md`
  - `PAPER-MAP.md`
- Scratch nearby:
  - `LeanProofs/Scratch/AuthorityScope.lean`
  - `LeanProofs/Scratch/PredicateWitnessSeparation.lean`
  - `LeanProofs/Scratch/NoFreeStandingReadout.lean`

Conceptual role: this cluster blocks local category errors. It proves that a
claim does not authorize unless all required local verdict dimensions are green,
and that mutation-side standing and claim-side authorization are separate proof
obligations.

### Witnessed derivation calculus

Role: the ratified, Mathlib-free public calculus for movement across typed
bridges.

- Defining files:
  - `LeanProofs/Witnessed.lean`
  - `LeanProofs/Witnessed/NoFreeLift.lean`
  - `LeanProofs/Witnessed/Derivation.lean`
  - `LeanProofs/Witnessed/Discipline.lean`
  - `LeanProofs/Witnessed/Embedding.lean`
  - `LeanProofs/Witnessed/Normalization.lean`
  - `LeanProofs/Witnessed/AxisIndependence.lean`
  - `LeanProofs/Witnessed/Obstruction.lean`
- Supporting objects:
  - `NoFreeLift.Lift`
  - `NoFreeLift.PaidFrom`
  - `NoFreeLift.no_free_lift`
  - `NoFreeLift.BridgeValid`
  - `NoFreeLift.paid_lift_sound`
  - `Derivation.derivation_extends_along_paid_path`
  - `Derivation.revoked_floor_derives_nothing`
  - `Discipline.cut_admissible_general`
  - `Discipline.WitnessedDiscipline`
  - `Discipline.discipline_metatheory`
  - `Embedding.freshness_bridge_valid`
  - `Embedding.embedded_lift_sound`
  - `Normalization.bridge_path_normal_form`
  - `Obstruction.bridgeValid_discriminating_iff_semanticNontrivial`
- Example/specimen files:
  - `LeanProofs/Witnessed/Examples.lean`, which imports only
    `LeanProofs.Witnessed` and checks the frozen public receipt names
- Docs/registers:
  - `experiments/no_free_lift_wiring/RATIFICATION-v1.3.md`
  - `docs/WITNESSED-FRONTIER-REGISTER.md`
  - `experiments/no_free_lift_wiring/WIRING-AUDIT.md`
  - `experiments/no_free_lift_wiring/ATLAS-MAP.md`
- Scratch nearby:
  - `LeanProofs/Scratch/NoSilentProjection.lean`
  - `LeanProofs/Scratch/NoFreeContinuation.lean`
  - bridge-price scratch files under `LeanProofs/Scratch/*BridgePrice.lean`

Conceptual role: this cluster owns paid movement. It is not a unifier for the
admissibility kernels. Its strongest public theorem shape is "no lift without a
kernel origin and paid bridge path"; its strongest fence is that normalization is
currently model-scoped to the freshness embedding.

### Refusal kernels

Role: ANNEX refusal surfaces that block a visible or local signal from being
treated as a stronger substantive witness.

- Defining files:
  - `LeanProofs/Admissibility/RecoveryMargin.lean`
  - `LeanProofs/Admissibility/ClosureEligibility.lean`
  - `LeanProofs/Admissibility/ConsolidationDenial.lean`
  - `LeanProofs/Admissibility/SurfaceAuthorization.lean`
  - `LeanProofs/Admissibility/DeferredWitness.lean`
- Supporting objects:
  - `RecoveryMargin.VisibleGreen`
  - `RecoveryMargin.RecoveryMargin`
  - `RecoveryMargin.visible_green_does_not_imply_recovery_margin`
  - `ClosureEligibility.verdict_closure_iff`
  - `ClosureEligibility.survival_alone_does_not_authorize_closure`
  - `ConsolidationDenial.fluency_does_not_witness_settlement`
  - `SurfaceAuthorization.collapsed_surface_denies_cause_specific_without_breaker`
  - `DeferredWitness.LawfulCompletion`
  - `DeferredWitness.firstViolation`
  - `DeferredWitness.statusOf`
  - `DeferredWitness.Admissible`
  - `DeferredWitness.pending_not_admissible`
  - `DeferredWitness.lapsed_not_admissible`
- Docs/registers:
  - `LeanProofs/Admissibility/README.md`
  - `WHAT-THIS-PROVES.md`
- Scratch nearby:
  - `LeanProofs/Scratch/BestEffortCompleteness.lean`
  - `LeanProofs/Scratch/LogOnlyProvesEmission.lean`
  - `LeanProofs/Scratch/PostHocLegitimationBridgePrice.lean`

Conceptual role: this cluster is not one theorem family yet. It has at least
three shapes already named by the repo: existential countermodel, conditional
rule, and lifecycle/classifier. The report should not flatten those shapes.

### Cross-boundary artifact specimens

Role: ANNEX artifact-family specimens around exposure minting, degradation
provenance, failure-to-exposure minting, and authorized cascade.

- Defining files:
  - `LeanProofs/Admissibility/CrossBoundaryExposure.lean`
  - `LeanProofs/Admissibility/CrossBoundaryDegradation.lean`
  - `LeanProofs/Admissibility/CrossBoundaryFailureMint.lean`
  - `LeanProofs/Admissibility/CrossBoundaryCascade.lean`
  - `LeanProofs/Admissibility/Composition.lean`
  - `LeanProofs/Admissibility/LocalBoundary.lean`
- Supporting objects:
  - `CrossBoundaryExposure.Exposure`
  - `CrossBoundaryExposure.Boundary`
  - `CrossBoundaryExposure.BoundaryPartition`
  - `CrossBoundaryExposure.NoInternalExternalExposure`
  - `CrossBoundaryExposure.no_external_exposure_without_authorized_edge`
  - `CrossBoundaryDegradation.toExposureConfig`
  - `CrossBoundaryDegradation.step_to_exposure_reach`
  - `CrossBoundaryDegradation.reach_to_exposure_reach`
  - `CrossBoundaryDegradation.no_external_degradation_from_internal_exposure`
  - `CrossBoundaryFailureMint.toExposureConfig`
  - `CrossBoundaryFailureMint.no_external_exposure_from_internal_failure`
  - `CrossBoundaryCascade.AuthorizedPath`
  - `CrossBoundaryCascade.step_to_exposure_reach`
  - `CrossBoundaryCascade.authorized_path_permits_endpoint_exposure`
  - `Composition.composition_preserves_safety_global_lift`
  - `LocalBoundary.MergeAdmissible`
  - `LocalBoundary.composition_preserves_global_safety_aperture`
- Docs/registers:
  - `LeanProofs/Admissibility/README.md`
  - `WHAT-THIS-PROVES.md`

Conceptual role: this cluster already has a repeated projection pattern from
richer artifacts back to `CrossBoundaryExposure`. `Composition` shows that global
boundary process syntax is not load-bearing; `LocalBoundary` names the aperture
where local authorization plus merge admissibility becomes the load-bearing
object.

### Safety bridge family

Role: ANNEX safety-axis family proving that authorization does not imply
defended-value preservation, and that a separate bridge predicate is required.

- Defining files:
  - `LeanProofs/Admissibility/AuthorizedNotSafe.lean`
  - `LeanProofs/Admissibility/AuthorizedNotSafeWitness.lean`
  - `LeanProofs/Admissibility/SafetyBridge.lean`
  - `LeanProofs/Admissibility/SafetyBridgeWitness.lean`
  - `LeanProofs/Admissibility/AuthorizedStepNotSafe.lean`
  - `LeanProofs/Admissibility/AuthorizedStepNotSafeWitness.lean`
  - `LeanProofs/Admissibility/SafetyTrajectory.lean`
  - `LeanProofs/Admissibility/AttestationLedger.lean`
- Supporting objects:
  - `AuthorizedNotSafe.authorized_not_safe`
  - `AuthorizedNotSafeWitness.authorized_not_safe_witnessed`
  - `SafetyBridge.SafetyEnv`
  - `SafetyBridge.SafetyPreserving`
  - `SafetyBridge.bridge_implies_safe`
  - `SafetyBridge.AuthStep`
  - `SafetyBridge.SafeStep`
  - `SafetyBridge.AuthorizedTraj`
  - `SafetyBridge.BridgedTraj`
  - `SafetyBridge.bridgedTraj_preserves`
  - `SafetyBridge.no_safeStep_for_unbridged_authStep`
  - `SafetyTrajectory.authorized_trajectory_loses_value`
  - `SafetyTrajectory.no_bridgedTrajC_to_poison_end`
  - `AttestationLedger.bridge_preserves`
  - `AttestationLedger.authorized_trajectory_loses_value`
  - `AttestationLedger.no_bridgedTraj_to_revoke_end`
- Docs/registers:
  - `LeanProofs/Admissibility/README.md`
  - `WHAT-THIS-PROVES.md`
  - `PAPER-MAP.md`

Conceptual role: this family is already internally coherent. Its wiring need is
mostly expository: make the safety axis easy to find without treating degenerate
all-green examples as substantive legitimacy.

### Root paper/specimen layer

Role: paper-facing specimens and formal claim audits. These are not contents of
the public admissibility surface.

- Defining files and objects:
  - `LeanProofs/TaxonomyGraph.lean`: `Reachable`,
    `structurally_terminal_exact`, `reachable_stays_in_closed`,
    `ds_not_reaches_dh`, `dk_not_reaches_dh`
  - `LeanProofs/BranchSelector.lean`: `BurnProfile`, `BSys`, `bstep`,
    `same_events_different_outcomes`, `priming_overrides_burn_profile`
  - `LeanProofs/PersistenceModel.lean`: `commitsToHysteretic`,
    `commitsToHysteretic_realizes`, `post_repair_trace_faster`
  - `LeanProofs/OpsMasking.lean`: `trajectory_eq_of_projected_eq`,
    `projection_masking`
  - `LeanProofs/Paper24SharedVision.lean`: paper-specific algebraic shard
  - `LeanProofs/Paper25EpistemicBorderControl.lean`:
    `ker_replicateRows_eq_ker`, `obsEquiv_policy_same`,
    `target_distinct_policy_same`
  - `LeanProofs/CollapsedSurface.lean`: `CollapsedAt`,
    `collapsed_surface_not_identified`
  - `LeanProofs/RepairOperator.lean`: `active_parked_disjoint`,
    `trichotomy`, `regimeClosed`
- Docs/registers:
  - `PAPER-MAP.md`
  - `CLAIM-REGISTER.md`
  - `WHAT-THIS-PROVES.md`

Conceptual role: these files pin paper claims and specimen kernels. Their
wiring value is explanatory crosswalk, not promotion into the admissibility
surface.

### P27 obligation skeleton

Role: unwired, post-transition obligation accounting skeleton.

- Defining file:
  - `LeanProofs/Admissibility.lean`
- Supporting objects:
  - `P27.admissible`
  - `P27.unaccounted_implies_inadmissible`
  - `P27.short_receipt_horizon_inadmissible`
  - `P27.open_finding_admissible_with_durability`
  - `P27.masked_recovery_not_resolved : True`
  - `P27.orphaned_causality_inadmissible : True`
- Docs/registers:
  - `README.md`
  - `LeanProofs/Admissibility/README.md`

Conceptual role: this is complementary to the authority kernel, not duplicate.
The repo explicitly says it is intentionally unwired and contains two `True`
placeholder discharges. It must not testify for doctrine.

## Stranded Lean objects

### `RefusalPropagation` as ANNEX rebar

- Source object: `LeanProofs/Admissibility/RefusalPropagation.lean`
- Existing definitions/theorems:
  - `Composition.BasisInheriting`
  - `Composition.refusal_composes`
  - `Composition.refusal_composes_two_hop`
  - `Composition.DependsTrans`
  - `Composition.refusal_propagates_transitively`
  - `ChainAdapter.State`
  - `ChainAdapter.Refused`
  - `ChainAdapter.BindingAdmissible`
  - `ChainAdapter.CascadeSound`
  - `ChainAdapter.RequiredFor`
  - `ChainAdapter.cascade_implies_basis_inheriting`
  - `Examples.ClaimAuthorizationProposal.downstream_proposal_cannot_bind_when_claim_basis_refused`
  - `Annex.NQDependency.disk_state_cannot_bind_when_device_enumeration_refused`
  - `Annex.NQDependency.disk_state_cannot_bind_via_refusal_composes`
- What it currently proves/models: if a basis-inheriting `requiredFor`
  relation holds, failure to witness an ancestor propagates to failure to
  witness a dependent claim. The chain adapter turns a binary refused/observable
  state plus `CascadeSound` into the `BasisInheriting` premise.
- Where it probably wants reuse: a future propagation kernel over the public
  authority path, especially `Derivation.BasisDerivation`,
  `Derivation.decideAuthority`, and `Execution.AuthorizedStep`.
- Why stranded: the file explicitly says that rising to a propagation kernel
  would require instantiating `requiredFor` and `witnesses` over existing kernel
  structure, and that step is not authorized in the probe.
- Missing edge classification: `PROMOTION_CANDIDATE`, operator-gated.
- Smallest useful next connection: an ANNEX specimen, not a public import,
  that reuses `ChainAdapter` over generic authority roles already used in
  `Examples.ClaimAuthorizationProposal`, with no claim that it instantiates
  `BasisDerivation` yet.

### `LocalBoundary` as aperture after `Composition`

- Source object: `LeanProofs/Admissibility/Composition.lean`
- Target object: `LeanProofs/Admissibility/LocalBoundary.lean`
- Existing definitions/theorems:
  - `Composition.Process`
  - `Composition.StepP`
  - `Composition.SystemReach`
  - `Composition.SafeProcess`
  - `Composition.any_process_safe_under_sealed_boundary`
  - `Composition.composition_preserves_safety_global_lift`
  - `LocalBoundary.RawStep`
  - `LocalBoundary.LocalAllows`
  - `LocalBoundary.ComponentStep`
  - `LocalBoundary.ComponentReach`
  - `LocalBoundary.MergeAdmissible`
  - `LocalBoundary.component_step_preserves_invariant`
  - `LocalBoundary.composition_preserves_global_safety_aperture`
- What it currently proves/models: `Composition` proves a global-boundary lift
  whose component safety hypotheses are not load-bearing. `LocalBoundary`
  removes the global oracle and makes `MergeAdmissible.left_sound` /
  `right_sound` the actual obligation.
- Where it probably wants reuse: a necessity pass for `MergeAdmissible`, using
  counterexamples that show a missing field can admit a locally authorized step
  that violates the merged partition.
- Why stranded: `LocalBoundary` itself marks the necessity claim as not yet
  proved and the bad cases as paper-shaped rather than theorem-shaped.
- Missing edge classification: `ANNEX_WIRING` for pressure tests;
  `PROMOTION_CANDIDATE` only with operator review.
- Smallest useful next connection: prove one load-bearing counterexample for
  dropping `left_sound` or `right_sound`, staying inside ANNEX.

### `DeferredWitness.firstViolation` and the refusal-shape taxonomy

- Source object: `LeanProofs/Admissibility/DeferredWitness.lean`
- Target object: refusal-kernel taxonomy in `LeanProofs/Admissibility/README.md`
- Existing definitions/theorems:
  - `DeferredWitness.LawfulCompletion`
  - `DeferredWitness.no_retroactive_standing`
  - `DeferredWitness.necromancy_rejected`
  - `DeferredWitness.mutated_terms_rejected`
  - `DeferredWitness.stale_evidence_rejected`
  - `DeferredWitness.Backflow`
  - `DeferredWitness.firstViolation`
  - `DeferredWitness.Status`
  - `DeferredWitness.statusOf`
  - `DeferredWitness.Admissible`
  - `DeferredWitness.pending_not_admissible`
  - `DeferredWitness.lapsed_not_admissible`
- What it currently proves/models: the one lawful late-witness completion path,
  a countable first-violation classifier, and a lifecycle where only
  `completed` is admissible.
- Where it probably wants reuse: docs should make clear that this is a third
  refusal-kernel shape, not an existential countermodel and not a simple
  conditional rule.
- Why stranded: the README explicitly says folding the third bucket into the
  catalog is a ratification act, not a registry count.
- Missing edge classification: `SAFE_WIRING` for audit documentation only;
  operator-gated for README taxonomy edits.
- Smallest useful next connection: cite the existing objects in this audit and
  avoid changing the taxonomy until operator approval.

### Merge-family seam

- Source objects:
  - `LeanProofs/Admissibility/ParameterizedMerge.lean`
  - `LeanProofs/Admissibility/ProjectionLaundering.lean`
  - `LeanProofs/Admissibility/BudgetMerge.lean`
  - `LeanProofs/Admissibility/StaleEvidenceMerge.lean`
  - `LeanProofs/Admissibility/MergeConflict.lean`
- Existing definitions/theorems:
  - `ProjectionLaundering.ErasesDefer`
  - `ProjectionLaundering.PreservesDefer`
  - `ProjectionLaundering.projection_launders_deferral`
  - `ProjectionLaundering.loss_aware_projection_blocks_deferral_laundering`
  - `ParameterizedMerge.MergeFrame`
  - `ParameterizedMerge.MergeRestoresValue`
  - `ParameterizedMerge.MergeComposesBridgedEndpoints`
  - `ParameterizedMerge.MergeRestoresBasis`
  - `ParameterizedMerge.MergeOkNecessaryAtValue`
  - `ParameterizedMerge.MergeOkNecessaryAtBasis`
  - `ParameterizedMerge.budgetFrame_restores`
  - `ParameterizedMerge.staleFrame_composes`
  - `ParameterizedMerge.staleFrame_value_necessity_fails`
  - `ParameterizedMerge.staleFrame_basis_necessity`
- What it currently proves/models: a parameterized merge frame over several
  candidate slices, with an explicit split between value restoration and basis
  restoration. The stale slice shows value-level necessity can fail while
  basis-level necessity remains meaningful.
- Where it probably wants reuse: future merge or deferral interfaces that need
  to distinguish value preservation from basis preservation.
- Why stranded: every listed merge file is `Custody-Class: UNRATIFIED-CANDIDATE`.
  `ParameterizedMerge` also documents known asymmetry rather than a settled
  universal interface.
- Missing edge classification: `PROMOTION_CANDIDATE`, operator-gated.
- Smallest useful next connection: no promotion. Keep as a candidate
  neighborhood; if touched, write a promotion-prep report that inventories which
  candidate theorems are load-bearing and which are only specimen-specific.

### `PublicReceiptRefinement` beside `SurfaceAuthorization`

- Source object: `LeanProofs/Admissibility/SurfaceAuthorization.lean`
- Target object: `LeanProofs/Admissibility/PublicReceiptRefinement.lean`
- Existing definitions/theorems:
  - `SurfaceAuthorization.Breaker`
  - `SurfaceAuthorization.authorize`
  - `SurfaceAuthorization.collapsed_surface_denies_cause_specific_without_breaker`
  - `SurfaceAuthorization.discriminator_licenses_cause_specific`
  - `PublicReceiptRefinement.Excludes`
  - `PublicReceiptRefinement.Refines`
  - `PublicReceiptRefinement.public_receipt_refines_observation`
  - `PublicReceiptRefinement.trivial_receipt_does_not_refine`
  - `PublicReceiptRefinement.contradictory_receipt_does_not_refine`
- What it currently proves/models: `SurfaceAuthorization` gates
  cause-specific authority; `PublicReceiptRefinement` defines a receipt as
  honest refinement when it excludes some cause but leaves at least one
  surface-admitted cause.
- Where it probably wants reuse: a bridge showing that a
  `[Breaker.preservedHistory]`-style recovery path should carry a `Refines`
  proof.
- Why stranded: `SurfaceAuthorization.Breaker` is an abstract enum, while
  `PublicReceiptRefinement.Refines` is abstract over receipt semantics. A direct
  theorem would commit receipt schema semantics that the files intentionally
  leave to consumers.
- Missing edge classification: docs-only or operator-gated ANNEX wiring.
- Smallest useful next connection: add docs-to-Lean pointers, not Lean theorem
  wiring.

### P27 obligation skeleton

- Source object: `LeanProofs/Admissibility.lean`
- Existing definitions/theorems:
  - `P27.admissible`
  - `P27.unaccounted_implies_inadmissible`
  - `P27.short_receipt_horizon_inadmissible`
  - `P27.open_finding_admissible_with_durability`
  - `P27.masked_recovery_not_resolved : True`
  - `P27.orphaned_causality_inadmissible : True`
- What it currently proves/models: post-transition obligation accounting with
  three real local proofs and two explicit placeholders.
- Where it probably wants reuse: no safe Lean reuse yet. It may inform future
  obligation-accounting vocabulary after substrate-accusation and causal-binding
  predicates are ratified.
- Why stranded: README and file header both state it is intentionally unwired;
  `H` is currently operationally inert at zero, and two theorem names are
  `True` placeholders.
- Missing edge classification: `DO_NOT_TOUCH`.
- Smallest useful next connection: none without operator review and real
  vocabulary.

## Repeated theorem shapes

### Surface signal does not witness substantive state

Current witnesses:

- `RecoveryMargin.visible_green_does_not_imply_recovery_margin`
- `ClosureEligibility.survival_alone_does_not_authorize_closure`
- `ConsolidationDenial.fluency_does_not_witness_settlement`
- `SurfaceAuthorization.collapsed_surface_denies_cause_specific_without_breaker`
- `DeferredWitness.pending_not_admissible`
- `DeferredWitness.lapsed_not_admissible`

Semantic dependency: each theorem refuses a stronger use of a weaker surface.
The shape is repeated, but not identical. The audit should not introduce a
single public `RefusalKernel` abstraction yet, because `DeferredWitness` is a
lifecycle/classifier shape and `SurfaceAuthorization` is a conditional rule,
not an existential countermodel.

### Projection from richer artifact family back to exposure containment

Current witnesses:

- `CrossBoundaryDegradation.toExposureConfig`
- `CrossBoundaryDegradation.step_to_exposure_reach`
- `CrossBoundaryDegradation.reach_to_exposure_reach`
- `CrossBoundaryFailureMint.toExposureConfig`
- `CrossBoundaryFailureMint.step_to_exposure_reach`
- `CrossBoundaryFailureMint.reach_to_exposure_reach`
- `CrossBoundaryCascade.toExposureConfig`
- `CrossBoundaryCascade.step_to_exposure_reach`
- `CrossBoundaryCascade.reach_to_exposure_reach`

Semantic dependency: richer artifact semantics are allowed only if their
exposure component projects to the original exposure containment theorem
`CrossBoundaryExposure.no_external_exposure_without_authorized_edge`.

This is a real repeated theorem shape. It wants a shared ANNEX helper only if a
fourth or fifth projection family appears. Abstracting now may hide constructor
discipline that is currently visible in each specimen.

### Authorization does not imply safety

Current witnesses:

- `AuthorizedNotSafe.authorized_not_safe`
- `AuthorizedNotSafeWitness.authorized_not_safe_witnessed`
- `SafetyBridge.bridge_implies_safe`
- `SafetyBridge.SafeStep`
- `SafetyBridge.bridgedTraj_preserves`
- `SafetyBridge.no_safeStep_for_unbridged_authStep`
- `SafetyTrajectory.authorized_trajectory_loses_value`
- `SafetyTrajectory.no_bridgedTrajC_to_poison_end`
- `AttestationLedger.authorized_trajectory_loses_value`
- `AttestationLedger.no_bridgedTraj_to_revoke_end`

Semantic dependency: the positive safety theorem routes through
`SafetyEnv.preserves` and `SafeStep.bridge`, not through `Allowed` or
`AuthorizedStep`. This pattern is already factored enough; the missing work is
not a new abstraction but clearer docs-to-Lean navigation and preservation of
the kernel-legible-vs-substantive legitimacy fence.

### No free movement without a paid bridge

Current witnesses:

- `Witnessed.NoFreeLift.Lift`
- `Witnessed.NoFreeLift.PaidFrom`
- `Witnessed.NoFreeLift.no_free_lift`
- `Witnessed.NoFreeLift.paid_lift_sound`
- `Witnessed.Embedding.embedded_lift_sound`
- `Witnessed.Embedding.cross_bridge_cannot_be_valid`
- `Witnessed.Embedding.cross_edge_dichotomy`
- `experiments/no_free_lift_wiring/WIRING-AUDIT.md`

Semantic dependency: any lifted claim traces to an origin and bridge path.
Scratch bridge-price files explore analogous "price of bridge" claims, but the
ratified calculus already owns the public paid-movement doctrine. Scratch should
not be used as testimony for this shape.

### Classifier plus one theorem per failing dimension

Current witnesses:

- `Authority.authorityVerdict` plus five blocking theorems
- `Freshness.Fresh` plus metric-time negative theorems
- `DeferredWitness.LawfulCompletion` plus `Backflow` and `firstViolation`
- `ClosureEligibility.verdict` plus `verdict_closure_iff`

Semantic dependency: a total classifier is useful when each negative outcome has
a theorem-shaped refusal. This is a repeated pattern, not yet a shared
interface. A generic interface would risk flattening domain-specific obligations.

## Missing intermediate abstractions

### Authority-level refusal propagation interface

- Implied by:
  - `RefusalPropagation.Composition.BasisInheriting`
  - `RefusalPropagation.Composition.refusal_composes`
  - `RefusalPropagation.ChainAdapter.cascade_implies_basis_inheriting`
  - `Derivation.BasisDerivation`
  - `Derivation.decideAuthority`
  - `Derivation.revoked_basis_never_authorized`
- Likely home: operator-gated ANNEX or a future separate propagation kernel.
- Minimal possible Lean shape, not to implement in this pass:

```lean
def KernelWitnesses (env : DerivationEnv) (state : GovState) :
    AuthorityClaim -> AuthorityClaim -> Prop := ...

def RequiredFor : AuthorityClaim -> AuthorityClaim -> Prop := ...

theorem authority_basis_inheriting :
    RefusalPropagation.Composition.BasisInheriting
      (KernelWitnesses env state) RequiredFor := ...
```

- What would be laundered if promoted too early: the meaning of "required for"
  in the public authority kernel. Without a kernel-owned theorem that a witness
  of `C` must witness `B`, `RequiredFor` is just a labeled graph edge.

### Local-boundary merge necessity

- Implied by:
  - `Composition.composition_preserves_safety_global_lift`
  - `LocalBoundary.MergeAdmissible`
  - `LocalBoundary.component_step_preserves_invariant`
  - `LocalBoundary.composition_preserves_global_safety_aperture`
- Likely home: ANNEX support.
- Minimal possible Lean shape, not to implement in this pass:

```lean
structure LeftUnsoundMergeWitness where
  lb1 lb2 lbm : LocalBoundary Domain
  e : Exposure Domain Failure
  allowed : LocalAllows lb1 (Action.expose e)
  violates : lbm.partition.Internal e.origin /\ lbm.partition.External e.target
```

- What would be laundered if promoted too early: the claim that
  `MergeAdmissible` is the necessary and complete merge interface. Current Lean
  proves sufficiency, not necessity.

### Refusal-kernel shape taxonomy

- Implied by:
  - `RecoveryMargin.visible_green_does_not_imply_recovery_margin`
  - `ClosureEligibility.survival_alone_does_not_authorize_closure`
  - `ConsolidationDenial.fluency_does_not_witness_settlement`
  - `SurfaceAuthorization.collapsed_surface_denies_cause_specific_without_breaker`
  - `DeferredWitness.firstViolation`
  - `Admissibility/README.md` taxonomy flag
- Likely home: docs only until operator ratification.
- Minimal possible shape, not to implement in Lean now:

```lean
inductive RefusalShape
  | existentialCountermodel
  | conditionalRule
  | lifecycleClassifier
```

- What would be laundered if promoted too early: count drift into doctrine. The
  README explicitly treats folding `DeferredWitness` into the taxonomy as a
  ratification act.

### Projection-to-exposure helper

- Implied by:
  - repeated `toExposureConfig`
  - repeated `step_to_exposure_reach`
  - repeated `reach_to_exposure_reach`
  - shared target `CrossBoundaryExposure.no_external_exposure_without_authorized_edge`
- Likely home: ANNEX support, once another richer artifact family demonstrates
  that the abstraction preserves visible constructor discipline.
- Minimal possible Lean shape, not to implement now:

```lean
structure ProjectsToExposure
    (RichConfig : Type) (RichStep : RichConfig -> RichConfig -> Prop) where
  toExposureConfig : RichConfig -> CrossBoundaryExposure.Config Domain Failure
  step_projects :
    RichStep c c' ->
    CrossBoundaryExposure.Reach B (toExposureConfig c) (toExposureConfig c')
```

- What would be laundered if promoted too early: constructor-level boundary
  checks. The current bespoke lemmas make it obvious which rich constructors
  project to exposure steps and which are inert.

### Classifier reflection (subsequently landed)

- Implied by:
  - `DeferredWitness.LawfulCompletion`
  - `DeferredWitness.firstViolation`
  - file comment naming `firstViolation u = none <-> LawfulCompletion u`
  - `DeferredWitness.statusOf`
- Current home: ANNEX. The audit's proposed shape subsequently landed:

```lean
theorem firstViolation_none_iff_lawful
    (u : LateWitnessUse) :
    firstViolation u = none <-> LawfulCompletion u := ...
```

- Runtime use still requires correspondence and admission review; that concern
  did not make consumer demand a prerequisite for the theorem.

### Receiver-relative verdict nucleus

- Implied by:
  - `Scratch/ConsumerRelativeVerdict.lean`
  - `Scratch/ConsumerRelativeFreshness.lean`
  - `Scratch/ConsumerRelativeForce.lean`
  - `Scratch/MultiConsumerAdoption.lean`
  - `Scratch/QuorumCustody.lean`
  - `Scratch/ShardedCustody.lean`
- Likely home: fenced scratch.
- Minimal possible Lean shape, not to promote:

```lean
abbrev Force (Verdict : Type u) : Type u := Consumer -> Artifact -> Verdict

def HasGlobalSection (force : Consumer -> Artifact -> Verdict) : Prop := ...
```

- What would be laundered if promoted too early: scratch receiver relativity
  into a public claim that all force/freshness/adoption/custody judgments share
  one semantics.

## Docs-to-Lean gaps

- `README.md` and `LeanProofs/Admissibility/README.md` counts are stale relative
  to `scripts/check-custody-classes.sh`. This is known count drift, not the
  semantic target of this audit.
- `LeanProofs/Admissibility/README.md` intentionally leaves one refusal-kernel
  taxonomy count stale pending operator sign-off on `DeferredWitness` as a third
  shape. The Lean witness is `DeferredWitness.firstViolation` plus `statusOf`;
  the missing edge is ratification, not proof search.
- `SurfaceAuthorization.lean` names recovery breakers while
  `PublicReceiptRefinement.lean` defines `Refines`. The docs say the doctrine
  connection exists, but no Lean theorem binds `Breaker.preservedHistory` to a
  `Refines` proof. That absence is probably correct until receipt schemas are
  consumer-owned.
- `docs/WITNESSED-FRONTIER-REGISTER.md` names normalization, cut-elimination,
  non-suppression, reachability classification, refusal legibility, and witnessed
  clocks. The concrete current witnesses are in `Witnessed/Normalization.lean`,
  `Witnessed/Discipline.lean`, `Witnessed/Derivation.lean`, and
  `Witnessed/Embedding.lean`; the frontier register should remain a fence, not a
  task queue.
- `PAPER-MAP.md` has a strong safety-bridge crosswalk, but `RefusalPropagation`
  and `LocalBoundary` are less legible there. A future docs pass could point to
  them as ANNEX apertures, not public doctrine.

## Scratch shapes that should remain scratch

- `LeanProofs/Scratch/ConsumerRelativeFreshness.lean`,
  `ConsumerRelativeForce.lean`, and `ConsumerRelativeVerdict.lean`: useful
  receiver-relative nucleus. Existing objects include `FreshFor`, `Force`,
  `ConsumersAgree`, `HasGlobalSection`, and
  `no_global_section_when_consumers_disagree`. Keep scratch.
- `LeanProofs/Scratch/MultiConsumerAdoption.lean`: proves
  `cross_consumer_adoption_does_not_imply`,
  `local_adoption_does_not_imply_global`, and
  `not_all_local_adoption_globalizes`. This is the cleanest scratch seed for
  receiver-relative refusal legibility. Keep scratch unless a separate
  custody review establishes an ANNEX-worthy formal delta.
- `LeanProofs/Scratch/QuorumCustody.lean`: models quorum intersection and
  custody limits. Current worktree has user modifications here; do not touch in
  this audit. Quorum intersection is explicitly not singular custody.
- `LeanProofs/Scratch/ShardedCustody.lean`: models shard-local admissibility
  and the lawful disjoint-shard exception via
  `disjoint_shards_allow_parallel_custody`. Keep scratch.
- `LeanProofs/Scratch/BridgeInterfaces.lean`: rich first-refusal ownership
  cascade with `BridgeDecision`, `CascadeOutcome`, and named refusal metadata.
  It is useful for interface imagination, but too feature-rich to promote.
- `LeanProofs/Scratch/Paper6TemporalClosureKernel.lean`: real proof-of-encodability
  around finite context, unbounded history, and autonomous ticks. It is a
  promising scratch neighborhood, not a wiring edge into the current kernels.
- `LeanProofs/Scratch/PostHocLegitimationBridgePrice.lean` and bridge-price
  siblings: useful price-theorem idiom; do not use as doctrine.
- `LeanProofs/Scratch/ProvenanceProfiles.lean` and custody profile scratch:
  operationally informative, but not canonical custody law.

## Safe wiring candidates

### Candidate 1: Semantic audit report only

- Classification: `SAFE_WIRING`
- Files involved: `SEMANTIC_WIRING_AUDIT.md` only
- Intended effect: make existing semantic joints visible without changing Lean,
  imports, custody markers, or README counts.
- Required commands:
  - `git status --short`
  - `lake build`
  - `lake build Witnessed`
  - `bash scripts/check-witnessed-footprint.sh`
  - `bash scripts/check-custody-classes.sh`
- Acceptance criteria:
  - report cites concrete files and named definitions/theorems;
  - no Lean files are edited;
  - count drift is recorded but not reconciled;
  - scratch is cited only as scratch.
- Authority risk: low.
- Worth doing now: it prevents the next build slice from confusing semantic
  wiring with import reachability.

### Candidate 2: RefusalPropagation generic specimen, still ANNEX

- Classification: `ANNEX_WIRING`
- Files likely involved:
  - `LeanProofs/Admissibility/RefusalPropagation.lean`
  - possibly `LeanProofs/Admissibility/README.md` for docs only
- Source object: `RefusalPropagation.ChainAdapter`
- Target object or missing interface: a generic authority-role specimen, not
  `Derivation.BasisDerivation`
- Exact objects involved:
  - `BasisInheriting`
  - `refusal_composes_two_hop`
  - `CascadeSound`
  - `RequiredFor`
  - `downstream_proposal_cannot_bind_when_claim_basis_refused`
- Intended effect: make the existing role-shaped example easier for downstream
  consumers to find, without claiming public-kernel instantiation.
- Required commands:
  - `lake build`
  - targeted `lake build LeanProofs.Admissibility.RefusalPropagation`
- Acceptance criteria:
  - no public aggregator import;
  - no custody change;
  - no claim that `requiredFor` is kernel-owned.
- Authority risk: medium. It becomes high if it starts mentioning
  `BasisDerivation` as discharged rather than future work.
- Worth doing now: this is the clearest stranded rebar in the repo.

### Candidate 3: LocalBoundary necessity pressure test

- Classification: `PROMOTION_CANDIDATE` until operator approves; implementation
  would be ANNEX-only
- Files likely involved:
  - `LeanProofs/Admissibility/LocalBoundary.lean`
  - optionally a new ANNEX test/specimen file if operator approves
- Source object: `LocalBoundary.MergeAdmissible`
- Target object or missing interface: load-bearing counterexample for dropping
  one merge obligation
- Exact objects involved:
  - `RawStep`
  - `LocalAllows`
  - `ComponentStep`
  - `MergeAdmissible.left_sound`
  - `MergeAdmissible.right_sound`
  - `composition_preserves_global_safety_aperture`
- Intended effect: distinguish sufficiency from necessity.
- Required commands:
  - `lake build`
  - targeted build for the touched module/file
- Acceptance criteria:
  - at least one theorem shows a weakened merge predicate permits a violation of
    `NoInternalExternalExposure`;
  - no claim of completeness;
  - no public surface import.
- Authority risk: medium-high. Necessity language is easy to overstate.
- Worth doing now: `Composition` already proved the previous composition theorem
  was diagnostic; this is the natural pressure test after that result.

### Candidate 4: DeferredWitness taxonomy pointer

- Classification: `SAFE_WIRING` if confined to docs; operator-gated if editing
  the taxonomy itself
- Files likely involved:
  - `SEMANTIC_WIRING_AUDIT.md`
  - optionally `LeanProofs/Admissibility/README.md` in a separate approved pass
- Source object: `DeferredWitness.firstViolation`
- Target object or missing interface: refusal-kernel shape taxonomy
- Exact objects involved:
  - `LawfulCompletion`
  - `Backflow`
  - `firstViolation`
  - `statusOf`
  - `Admissible`
- Intended effect: make the third-shape evidence legible without ratifying it.
- Required commands:
  - docs-only pass: no Lean-specific command beyond `lake build` sanity
- Acceptance criteria:
  - no count reconciliation bundled with semantic ratification;
  - no theorem claim that `firstViolation u = none <-> LawfulCompletion u`
    exists unless it is actually proved.
- Authority risk: low for audit docs, high for README taxonomy changes.
- Worth doing now: prevents future count-fixing from accidentally becoming
  doctrine-fixing.

### Candidate 5: Receiver-relative refusal legibility scratch expansion

- Classification: `SCRATCH_EXPANSION`
- Files likely involved:
  - `LeanProofs/Scratch/ConsumerRelativeVerdict.lean`
  - `LeanProofs/Scratch/ConsumerRelativeFreshness.lean`
  - `LeanProofs/Scratch/ConsumerRelativeForce.lean`
  - `LeanProofs/Scratch/MultiConsumerAdoption.lean`
  - `LeanProofs/Scratch/QuorumCustody.lean`
  - `LeanProofs/Scratch/ShardedCustody.lean`
- Source object: receiver-relative scratch cluster
- Target object or missing interface: none in public Lean; scratch-only
  exploration of refusal legibility
- Exact objects involved:
  - `HasGlobalSection`
  - `ConsumersAgree`
  - `FreshFor`
  - `cross_consumer_adoption_does_not_imply`
  - `local_adoption_does_not_imply_global`
  - `Quorum`
  - `disjoint_shards_allow_parallel_custody`
- Intended effect: collect and sharpen receiver-relative theorem shapes without
  moving them out of scratch.
- Required commands:
  - targeted builds for scratch files touched
  - `lake build` if root behavior might be affected
- Acceptance criteria:
  - `Custody-Class: SCRATCH` remains;
  - no root import;
  - no README promotion language.
- Authority risk: medium if scratch names start sounding canonical.
- Worth doing now: this is the best scratch neighborhood for the frontier
  register's receiver-facing refusal legibility track.

## Operator-gated candidates

- Public or semi-public refusal propagation over `Derivation.BasisDerivation` and
  `decideAuthority`: gated because it would define what "required basis" means
  inside the authority kernel.
- `LocalBoundary` necessity or completeness claims: gated because current Lean
  proves sufficiency only.
- Refusal-shape taxonomy update adding `DeferredWitness` as lifecycle/classifier:
  gated because the README explicitly says this is a ratification act.
- Any merge-family promotion from `UNRATIFIED-CANDIDATE` to ANNEX: gated because
  `ParameterizedMerge` records known asymmetry and candidate-level semantics.
- Any P27 wiring: gated because of `True` placeholders and inert horizon
  semantics.
- Any public Witnessed 2.0 frontier item: gated by
  `docs/WITNESSED-FRONTIER-REGISTER.md`; current frontier entries are named,
  not authorized.

## Do-not-touch list

- Do not edit public aggregators for this audit:
  - `LeanProofs.lean`
  - `LeanProofs/Witnessed.lean`
  - `LeanProofs/Admissibility/AdmissibilityKernels.lean`
- Do not reconcile custody counts in this pass.
- Do not import scratch into root or ANNEX.
- Do not promote:
  - `LeanProofs/Scratch/BridgeInterfaces.lean`
  - receiver-relative scratch files
  - bridge-price scratch files
  - `LeanProofs/Scratch/Paper6TemporalClosureKernel.lean`
  - P27 placeholders in `LeanProofs/Admissibility.lean`
- Do not treat `Witnessed/Examples.lean` `#check`s, marker theorem
  `kernels_compile`, or P27 `True` theorems as substantive evidence.
- Do not edit `LeanProofs/Scratch/QuorumCustody.lean` during this audit; it was
  already modified before this pass.

## Top 3 next Codex prompts

### 1. Safest immediate wiring slice

```text
Create a docs-only semantic wiring follow-up from SEMANTIC_WIRING_AUDIT.md.

Scope:
- Add or refine docs-to-Lean pointers only.
- Focus on RefusalPropagation, LocalBoundary, DeferredWitness, and the safety bridge family.

Forbidden moves:
- Do not edit Lean files.
- Do not change imports.
- Do not reconcile custody counts.
- Do not promote scratch.
- Do not commit.

Files to inspect:
- SEMANTIC_WIRING_AUDIT.md
- LeanProofs/Admissibility/README.md
- README.md
- docs/WITNESSED-FRONTIER-REGISTER.md
- PAPER-MAP.md

Expected outputs:
- A docs patch or a no-change report.
- Every new docs claim must cite an existing Lean definition/theorem or explicit custody fence.

Commands to run:
- git status --short
- lake build
- lake build Witnessed
- bash scripts/check-witnessed-footprint.sh
- bash scripts/check-custody-classes.sh

Stop conditions:
- Stop if the docs change would require deciding a promotion boundary.
- Stop if any claim depends on scratch as authority.
```

### 2. Best scratch expansion slice

```text
Expand receiver-relative refusal legibility in SCRATCH only.

Scope:
- Work only under LeanProofs/Scratch/.
- Inspect ConsumerRelativeVerdict, ConsumerRelativeFreshness, ConsumerRelativeForce,
  MultiConsumerAdoption, QuorumCustody, and ShardedCustody.
- Add at most one small scratch specimen that clarifies receiver-relative refusal
  or quorum/custody non-globalization.

Forbidden moves:
- Do not import scratch into LeanProofs.lean.
- Do not change custody class.
- Do not move files.
- Do not claim public doctrine.
- Do not touch non-scratch Lean files.

Expected outputs:
- Scratch theorem specimens, or a report explaining why no theorem should be added.
- A short comment in the scratch file naming what remains unpromoted.

Commands to run:
- lake build <targeted scratch module if applicable>
- lake build

Stop conditions:
- Stop if the theorem needs a public interface.
- Stop if the proof would require treating consumer-relative scratch vocabulary
  as canonical.
- Stop if LeanProofs/Scratch/QuorumCustody.lean has unrelated user edits that
  would be overwritten.
```

### 3. Best operator-gated promotion-prep slice

```text
Prepare a LocalBoundary necessity pressure-test plan or ANNEX theorem candidate.

Scope:
- Inspect Composition.lean and LocalBoundary.lean.
- Target one pressure test showing that a weakened MergeAdmissible obligation
  permits a locally authorized component step that violates the merged partition.
- Keep the work ANNEX-only unless operator explicitly approves a broader boundary.

Forbidden moves:
- Do not edit AdmissibilityKernels.lean.
- Do not add public imports.
- Do not change custody classes.
- Do not claim MergeAdmissible is complete.
- Do not generalize beyond the existing Exposure/BoundaryPartition vocabulary.

Files to inspect:
- LeanProofs/Admissibility/Composition.lean
- LeanProofs/Admissibility/LocalBoundary.lean
- LeanProofs/Admissibility/CrossBoundaryExposure.lean

Expected outputs:
- Either a small ANNEX theorem candidate or a failed-boundary report.
- Explicit statement of which MergeAdmissible field is load-bearing.

Commands to run:
- lake build LeanProofs.Admissibility.LocalBoundary
- lake build

Stop conditions:
- Stop if the proof requires new doctrine rather than existing definitions.
- Stop if the counterexample needs a richer process calculus.
- Stop if the result starts reading as public-kernel promotion.
```
