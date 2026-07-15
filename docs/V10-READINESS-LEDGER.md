# v10 Readiness Ledger — View Semantics and Bounded Projection

**Status: GATE-COMPLETE / OPERATOR-ACCEPTED, RELEASE-PREPPED (2026-07-14).
Tag, GitHub release, and DOI remain operator actions.**

This is the as-built evidence ledger requested by
[`V10-GAP-SPEC.md`](V10-GAP-SPEC.md). It is not a tag, GitHub release, DOI,
or custody promotion. Written 2026-07-14 as GATE-COMPLETE CANDIDATE /
UNMINTED with the repository still advertising `9.0.0`; later the same day
the operator accepted the ledger and directed the v10 metadata transition
(lakefile `10.0.0`, CHANGELOG 10.0.0 entry, CITATION.cff title + abstract +
version + date, README current-release section). The mint itself — tag,
GitHub release creation, Zenodo deposit — is the operator's, and no custody
class changes at mint.

## Candidate release claim

The landed surface supports the following bounded claim:

> Finite view systems admit a sound-and-complete, two-axis audit of
> operational sufficiency and declared disclosure bounds. Weak
> nondetermination can fail under composition while declared bounds compose;
> deterministic bounded projection has an exact refinement characterization;
> and view refinement changes distinguishability without minting transition
> authority. Binding-source ablation instantiates the shared semantics beyond
> XOR. In the resident bridge ontology, disclosure is an orthogonal view-context
> axis, not a sixth family atom.

No broader information-flow, noninterference, probabilistic leakage,
side-channel, runtime-compliance, or transition-authority claim is included.

## Gate A — semantic core earned

| Requirement | Landed receipt |
| --- | --- |
| Shared semantics | `View`, `Indistinguishable`, fine-to-coarse `Refines`, `Determines`, `NotFullyDetermining`, and `FiberwiseAmbiguous` in `ViewSemantics/Core.lean` |
| Weak/strong boundary | `fiberwiseAmbiguous_notFullyDetermining` with explicit `Nonempty`; closed three-world non-converse in `WeakNotStrongCounterexample` |
| Composition laws | `compose_indistinguishable_iff`, `refines_compose_iff`, `compose_mono`, and `determines_compose_iff`; `finiteJoin` and `refines_finiteJoin` expose the finite-family API |
| Rooted nonclosure witnesses | `CompositionCounterexample.weak_nondetermination_not_closed_under_compose`; strong two-component and six-premise three-component fiberwise receipts |
| Existing abstraction reuse | `ConsequencePartition.Refines` and `FactorsThrough` now wrap the canonical core; `Adapters.lean` bridges ConsequencePartition, CollapsedSurface, and WitnessInvariance |
| P25 reuse | `P25Adapter.obsEquiv_iff_indistinguishable` and `observationPolicy_determined`, isolated in `ViewSemanticsMathlibIslands` |
| Existing specimens | `MosaicRelease` is a compatibility/regression wrapper over the rooted composition fixture; `CompartmentConflict` uses canonical bounded-projection definitions and proves fiberwise payload ambiguity |
| Four audit cells | `Examples.all_four_disclosure_sufficiency_cells_inhabited` covers within/insufficient, within/sufficient, exceeded/sufficient, and exceeded/insufficient |

## Gate B — bounded projection earned

| Requirement | Landed receipt |
| --- | --- |
| Exact deterministic sandwich | `deterministicallyBoundedSufficient_iff_refinement_sandwich` |
| General-safe fence | `OperationallySufficient` remains existential; `operationallySufficient_required_determines` is one-way, and the converse requires an explicit total factorization map |
| Existence boundary | `deterministic_bounded_projection_exists_iff` and constructive `bounded_action_projection_exists_iff`; both choose the required-action projection, not the budget |
| Bound composition | `withinDisclosureBound_compose` and `withinDisclosureBound_finiteJoin`; distinct from the rooted XOR nondetermination countermodel |
| Actual five-atom audit | `NoSilentProjectionAxis.canDischarge_iff_carries` imports the resident `Atom`, `Family`, `CanDischarge`, and `FamilyDischarges` ontology rather than recreating five proposition fields |
| Negative ontology result | `no_resident_bridge_pair_pays_all_five`: with empty conversion and no source family carrying all five, the literal all-five bridge premise is uninhabited |
| Orthogonal-axis adjudication | `exact_projection_bridge_different_view_verdicts` indexes two sufficient contexts by one exact self-discharging Projection bridge; only one is within budget. `disclosure_is_orthogonal_to_resident_bridge_ontology` records the scoped verdict |

This is deliberately not a sixth `Atom` constructor. The resident enum is
family-indexed, while a disclosure bound is recipient/context-indexed by both a
budget and a view. A future ontology that explicitly carries those parameters
could internalize the condition; this candidate proves only the current
architecture.

## Gate C — release argument earned

### Finite checker

`FiniteChecker.lean` uses explicit complete lists of worlds and actions. Its
public `ViewAudit` retains two independent typed results:

- `PolicyCertificate` or `ActionConflict`; the conflict contains an inhabited
  observation fiber and, for every action, a concrete same-fiber world that
  rejects it.
- `BoundCertificate` or `ForbiddenDistinction`; the latter contains concrete
  worlds equal under the budget and unequal under the view.

`checkActionability_*_iff` and `checkDisclosure_*_iff` prove soundness and
reflection in both directions. `FiniteCheckerExamples.all_four_checker_cells_evaluate`
executes all four quadrants without `native_decide` or a collapsed validity bit.

### Authorized-trace custody

`DynamicTraceAdapter.AuthorizedRun` consumes an existing v9
`AuthorizedTrace`. `refineObservation_reuses_trace` and
`joinObservation_reuses_trace` preserve that exact evidence and step sequence.
The separation receipts `full_visibility_does_not_override_revoked_basis` and
`full_visibility_does_not_supply_missing_authority` reuse the v9 walls:
greater visibility does not construct an `AuthorizedStep`, `DynamicStep`, or
`AuthorizedTrace`.

### Non-XOR application

`ViewSemantics.Applications.BindingSourceAblation` factors the source
`TraceDetermined` predicate exactly through canonical `Determines` using the
quotient governed-trace view. The closed two-plant application proves intact
trace fibers remain ambiguous about viability coupling, while actual gate
ablation strictly refines the observation and determines that coupling. These
worlds are intervention-specific plants and governed traces, not XOR bits.

## Import and custody map

| Target/root | Contents | Custody boundary |
| --- | --- | --- |
| `ViewSemantics` | Core, bounded projection, rooted composition fixtures, four cells, generic adapters, generic bridge/view split, finite checker, authorized-trace adapter | Default, Mathlib-free, `UNRATIFIED-CANDIDATE`; forbidden from importing Applications or Scratch |
| `ViewSemanticsApplications` | BindingSourceAblation application and actual NoSilentProjection atom/axis adjudication | Default, Mathlib-free application/annex root; raw sources remain `SCRATCH` |
| `ViewSemanticsMathlibIslands` | P25 observation adapter | Explicit non-default Mathlib island; `UNRATIFIED-CANDIDATE` |
| `LeanProofs.lean` | Existing aggregate | Unchanged import boundary; candidate roots are not silently promoted here |

`Scratch/NoSilentProjection.lean` predates the six-file inventory below. It is
an allowlisted source dependency of the actual-ontology adapter only. It keeps
`Custody-Class: SCRATCH`; import and build contact do not promote it.

## Complete post-v9 six-file inventory (as of candidate commit `6f5e6b8`)

| File | Provenance | Actual disposition |
| --- | --- | --- |
| `MosaicRelease.lean` | `06f9800`, 2026-07-10 | Generic definitions superseded by canonical Core/CompositionCounterexample. Retained as a directly checked `SCRATCH` compatibility/regression wrapper; weak receipts are corollaries of rooted strong fiberwise theorems. Not imported by the candidate root. |
| `CompartmentConflict.lean` | `06f9800`, 2026-07-10 | Generic determination definition superseded by canonical Core. HAL, typed refusal, and narrow-disclosure fixtures retained in `SCRATCH`; now exposes canonical insufficiency, bounded-sufficiency, and fiberwise payload receipts. Not directly promoted. |
| `BindingSourceAblation.lean` | `c8235e2`, updated by `c0b60b9`, 2026-07-10 | Selected non-XOR source. Left `SCRATCH`, explicitly rooted only as the unchanged dependency of the `UNRATIFIED-CANDIDATE` application adapter. |
| `RegulatorRecovery.lean` | `c0b60b9`, 2026-07-10 | Retained as an unrooted `SCRATCH` application/annex candidate. Superseded by neither the selected application nor the core; explicitly deferred from v10 scope. |
| `SelfEntrenchment.lean` | `f690312`, 2026-07-12 | `SCRATCH`; explicitly deferred to the reversal-authority campaign. |
| `BorrowedSpend.lean` | `b9f960f`, 2026-07-12 | `SCRATCH`; explicitly deferred to the credit/standing campaign. |

Inventory is classification, not a demand to absorb all six files.

### Post-candidate additions (after `6f5e6b8`, outside the release claim)

The completeness claim above is scoped to the candidate commit. Two commits
landed after it and before release-prep:

| Commit | Contents | Disposition |
| --- | --- | --- |
| `bdf714f` (adjudication provenance) | Provenance notes for the sixth-atom adjudication | Documentation; no proof-surface change |
| `eb1ee75` (codex audit + scraps) | New `SCRATCH` incubations — `SignalAuthority`, `StatusConversionBinding`, `CommitmentStanding`, `ConsolidationController`, `AffectiveCouplingClassification` — plus expanded `NoSilentProjection` and header/doc touch-ups across Admissibility and Scratch | All `SCRATCH`, unrooted from the candidate targets; custody and isolation gates pass; ship in the archive, testify for nothing |

A 2026-07-14 formalization-leads-code doc/header sweep (comment-only; no
proof content) landed in the same release-prep window. None of these enter
the candidate release claim; they are listed so this inventory's
"complete" is honest about its cut point.

## Trust and executable audit

`scripts/check-viewsemantics-footprint.sh` currently attests:

- 36 structural, composition, bounded-projection, reuse, atom-axis, checker,
  and Scratch compatibility receipts with no axioms;
- BindingSourceAblation exactly `[propext, Quot.sound]`;
- P25 exactly `[propext, Classical.choice, Quot.sound]`; and
- trace reuse/separation receipts with exactly the footprints of the v9 trace
  and authorization walls they consume. The latter include `propext` and the
  already classified abstract v9 state/authority signatures; the adapter adds
  no new foundation.

The isolation gate separately proves the shared and application closures are
Mathlib-free and custody-separated, with P25 confined to its explicit island.
Repository-wide axiom classification remains 23 signature, 8 specimen, zero
interface-law, zero forbidden, and zero unclassified declarations.

## Verification envelope

The following passed on 2026-07-14 in the repository toolchain:

```text
lake build
lake build LeanProofs AdmissibilityMathlibIslands ViewSemanticsMathlibIslands
lake build ViewSemantics ViewSemanticsApplications ViewSemanticsMathlibIslands
lake env lean LeanProofs/Admissibility/ConsequencePartition.lean
lake env lean <each of the six post-v9 Scratch files>

scripts/check-viewsemantics-footprint.sh
scripts/check-viewsemantics-isolation.sh
scripts/check-witnessed-footprint.sh
scripts/audit-axioms.sh
scripts/audit-native-decide.sh
scripts/check-custody-classes.sh
scripts/check-mathlib-pin.sh
scripts/check-mathlib-free-targets.sh
git diff --check
```

## Minting boundary

Gate C earns a release argument; it does not perform the external release.
Before minting, the operator must accept this ledger and separately authorize
the v10 version/CFF/changelog/README transition, tag, GitHub release, and DOI.
None of those mutations has been made in this campaign working tree.
