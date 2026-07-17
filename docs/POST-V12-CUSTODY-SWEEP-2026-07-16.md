# Post-v12 ANNEX / Scratch Custody Sweep

**Status:** historical discovery/decision ledger.  This records the first
post-v12 ANNEX/Scratch pass before migration work began.  Its original counts
and proposed dispositions are preserved as audit history; the broader
candidate/unmarked audit and final release disposition are recorded in
[`V13-RELEASE-LEDGER.md`](V13-RELEASE-LEDGER.md).  Baseline: `v12.0.0`,
commit `b528af8`, 2026-07-16.

> **Post-audit correction.** The first pass covered the 54 ANNEX and 103
> Scratch artifacts but treated 45 `UNRATIFIED-CANDIDATE` modules as later
> work.  The v13 pass did not preserve that exception: it audited the full 271
> tracked Lean files and classified the 108 candidate or previously unmarked
> modules as 24 stable API, 44 public evidence, 11 skunkworks, and 29
> historical.  The combined migration had 53 live skunkworks transfers, four
> of them Mathlib-bound. All 53 are now complete and sibling-audited, including
> the four explicit Mathlib-island joins; their public originals are deleted.
> Therefore
> the sentence near the end of this document
> saying those 45 modules are “outside this requested sweep” is superseded,
> not a current instruction.

## Decision

Retire `ANNEX` and `Scratch/` as live public-repository custody lanes.
Incubation belongs in the sibling skunkworks.  The public repository retains
two distinct terminal roles:

1. **stable API** — compatibility-bearing public definitions and theorems in
   an exact stable-root closure;
2. **public evidence** — finished examples, countermodels, audit fossils, and
   release specimens in exact evidence targets, outside stable roots.

Both roles may use `Custody-Class: PUBLIC-SHIPPED`; exact root/evidence
registries must distinguish them.  A green build remains regression coverage,
not promotion.

This sweep therefore does not send every non-kernel theorem to skunkworks.
Finished public evidence is a terminal public disposition, not failed or
half-finished API work.

## Mechanical baseline

- There are 54 semantic ANNEX modules: 44 with the literal machine marker and
  ten `Witnessed` modules whose prose header says `Custody class: ANNEX`.
- There are 103 Scratch artifacts: 101 under `LeanProofs/Scratch` and two
  (`BoundaryWitness`, `GuardCollapse`) under `LeanProofs/Admissibility`.
- All 103 Scratch artifacts elaborate directly with `lake env lean`; there
  were zero failures.
- `lake build BoundedCalculi Witnessed PaidRecompositionEvidence
  JudgmentOrientationExamples` passes.
- `lake build CustodyIndexedSequents ViewSemanticsApplications
  PaidRecompositionEvidence` passes.
- No `PUBLIC-SHIPPED` module directly imports Scratch.
- The only non-Scratch-to-Scratch edges are:
  - paid evidence `FiniteSupportOneCrossing` to `FiniteSupportChecker`;
  - two ViewSemantics application adapters to `BindingSourceAblation` and
    `NoSilentProjection`.
- The current custody gate examines only 84 of 244 Lean modules.  It passes
  while 36 modules have no exact recognized marker.  Seven files in the
  Scratch directory lack the literal marker: `AggregateWitnessRequiresJoin`,
  `BoundaryTransit`, `ExecutionRevalidation`, `LogOnlyProvesEmission`,
  `NoFreeContinuation`, `Paper6TemporalClosureKernel`, and
  `SurfaceDeformationRequiresCoupling`.
- `BreakGlassAuthorization.lean` is tracked.  Nothing is untracked.

## ANNEX disposition — all 54 modules

### Correct stable-closure classification — 10

The public `LeanProofs.Witnessed` root already imports these modules.  They are
de facto stable substrate and should be marked `PUBLIC-SHIPPED` unchanged:

- `Witnessed/Formula`
- `Witnessed/Gentzen`
- `Witnessed/HeadOnlyGentzenCutFailure`
- `Witnessed/ResourceCheckerExec`
- `Witnessed/LaunderingCorpus`
- `Witnessed/Normalization`
- `Witnessed/Discipline`
- `Witnessed/AxisIndependence`
- `Witnessed/CommutesNecessity`
- `Witnessed/Obstruction`

`HeadOnlyGentzenCutFailure`, `LaunderingCorpus`, and `Obstruction` are better
long-term residents of a `WitnessedEvidence` target than the stable root.  That
is optional root surgery, not a reason to leave their present classification
false.  The other seven are live public calculus/checker content.

### Public stable-family promotions — 3

These are coherent, green, dependency-clean theorem families rather than
incubation:

- `Admissibility/SafetyBridge` — generic safety bridge primitive;
- `Admissibility/DynamicTrace`;
- `Admissibility/FreshnessDynamicTrace`.

The dynamic pair was the v9 headline and should receive its own exact public
root.  `SafetyBridge` should be the API core of its family; its concrete wounds
and witnesses belong in evidence.

### Public Bounded Calculi release family — 11

All eleven are the already-audited v3 release object.  Reclassify all as
`PUBLIC-SHIPPED`.  The tag did not itself promote them; their finished,
audited, unchanged surface now earns a terminal public classification:

- `BoundedCalculi` (aggregate compile marker)
- `BoundedCalculi/BootKernel`
- `BoundedCalculi/BoundaryArtifact`
- `BoundedCalculi/CheckpointSettlement`
- `BoundedCalculi/ExecutionCustody`
- `BoundedCalculi/MeasureAccounting`
- `BoundedCalculi/ObligationResidue`
- `BoundedCalculi/RefusalDenial`
- `BoundedCalculi/SafetyPreservation`
- `BoundedCalculi/SurfaceProjection`
- `BoundedCalculi/TemporalCustody`

Likely compatibility core: `TemporalCustody`, `SurfaceProjection`,
`RefusalDenial`, `ObligationResidue`, `ExecutionCustody`,
`CheckpointSettlement`, and supporting `MeasureAccounting`.  Keep the
aggregate, `BoundaryArtifact`, `SafetyPreservation`, and `BootKernel` as public
release evidence until their surrogate/toy portions are split or deliberately
accepted as API.

### Public Admissibility evidence — 24

These are finished theorem families, concrete policies, countermodels, or
examples.  Reclassify as public evidence; do not add them wholesale to
`AdmissibilityKernels`:

- `Admissibility/AttestationLedger`
- `Admissibility/AuthorityScope`
- `Admissibility/AuthorizedNotSafe`
- `Admissibility/AuthorizedNotSafeWitness`
- `Admissibility/AuthorizedStepNotSafe`
- `Admissibility/AuthorizedStepNotSafeWitness`
- `Admissibility/AxisSkew`
- `Admissibility/ClosureEligibility`
- `Admissibility/Composition`
- `Admissibility/ConsolidationDenial`
- `Admissibility/CorrectiveBoundary`
- `Admissibility/CrossBoundaryCascade`
- `Admissibility/CrossBoundaryDegradation`
- `Admissibility/CrossBoundaryExposure`
- `Admissibility/CrossBoundaryFailureMint`
- `Admissibility/DeferredWitness`
- `Admissibility/Examples`
- `Admissibility/FiatAdmissibility`
- `Admissibility/NumericalAdmissibility`
- `Admissibility/PredicateWitnessSeparation`
- `Admissibility/PublicReceiptRefinement`
- `Admissibility/RecoveryMargin`
- `Admissibility/SafetyBridgeWitness`
- `Admissibility/SafetyTrajectory`

The four `CrossBoundary*` modules are a coherent Mathlib island and may later
receive a stable island root.  `FiatAdmissibility`,
`NumericalAdmissibility`, and `AxisSkew` are a coherent classifier family, but
their concrete policy tables should not become compatibility promises by
accident.  The remaining safety modules are evidence for `SafetyBridge`, not
additional generic policy.  `PublicReceiptRefinement` also requires an
explicit disposition for its currently unmarked `LeanProofs.CollapsedSurface`
dependency before the whole-tree gate can admit the public evidence closure.

### Other public evidence — 4

- `JudgmentOrientation/Examples` — v12 examples/countermodels target;
- `Witnessed/PaidRecomposition/Applications/ResourceTraceOneCrossing` — v11 evidence;
- `Witnessed/PaidRecomposition/Countermodels/EndpointCompleteness` — v11 evidence;
- `Witnessed/PaidRecomposition/Applications/FiniteSupportOneCrossing` — v11 evidence,
  after the finite-support Scratch closure is rehomed as public substrate.

`FiniteSupportOneCrossing` is not a skunkworks result.  Its direct dependency
is classification debt in the released v4-v7 checker family; correcting that
closure removes the v12 symbolic Scratch exception.

### Move to skunkworks — 2

- `Admissibility/LocalBoundary` — explicitly incomplete `_aperture`, deferred
  completeness/bad cases, and a dependency on unratified
  `ReachabilityClosure`; move with `LocalBoundaryPressure` in the later
  candidate sweep.
- `Admissibility/RefusalPropagation` — mixed generic law and tool-named
  fixtures; extract the generic theorem there if it earns a return.  Repair
  the current AG/NQ/RRP crosswalk citations as part of the move.

## Scratch disposition — all 103 artifacts

### Corrective public promotion: v4-v7 stable family — 17

These are the exact released headline modules.  They are green, audited,
semantically scoped by four release ledgers, free of speculative dependencies,
and already consumed by later public/private work.  Promote/rehome them as one
unchanged public family:

- `BridgeSequent`
- `ExecutionSequent`
- `ExecutionObligationSequent`
- `BridgeCompositionSequent`
- `CustodyIndexedSequent`
- `StructuralPolicySequent`
- `EvidenceCalculusSequent`
- `DerivationData`
- `StructuralNormalization`
- `LinearNormalization`
- `OccurrenceTrace`
- `DecidableScreens`
- `TracedCoherence`
- `FiniteSupportChecker`
- `ArtifactProfiles`
- `ProfileStages`
- `JurisdictionScreen`

This is corrective recognition, not new mathematical content.  In particular,
the exact twelve-module closure ending at `FiniteSupportChecker` is consumed by
v11 paid evidence and by skunkworks PC-0.  Moving it to skunkworks would invert
the recorded source-of-truth relation.

### Public support/evidence for the v4-v7 family — 7

Four modules are imported by the released family and therefore must move with
it, but need not be advertised as compatibility API:

- `TemporalSurfaceAdapter`
- `TemporalToSurfaceBridgeWiring`
- `Zoo`
- `OverlapAudits`

Three independent released specimens are terminal public evidence:

- `CaveatSequent`
- `DeltaTSequent`
- `FluencySequent`

### PathVerdict public family — 4

Promote/rehome as stable generic API:

- `PathVerdict/Core`
- `PathVerdict/Edges`

Retain as terminal public evidence:

- `PathVerdict/StandardObstructions`
- `PathVerdict/EvidencePromotionCoverage`

Core and Edges were deliberately extracted from skunkworks as Tier-1 public
source, and the private parity manifest names this repository as source of
truth.  Their lingering `Scratch` path is pure classification debt.

### v10 application evidence — 4

Retain as public evidence/application dependencies, not generic API:

- `BindingSourceAblation`
- `NoSilentProjection`
- `MosaicRelease`
- `CompartmentConflict`

The first two are imported by the ViewSemantics application adapters; the
other two are frozen in the v10 footprint gate.  Rehome source and adapters
atomically.  The separate `UNRATIFIED-CANDIDATE` sweep must decide the
ViewSemantics stable/evidence roles around them.

### Finished public specializations — 2

Add exact evidence build/footprint receipts, then promote as terminal public
evidence:

- `NoSilentDelta`
- `CrossingBalance`

They specialize the released v5-v7 machinery and introduce no speculative
generic API.

### Promotion-ready coherent bundle — 4

Promote together as a named public evidence/library bundle after choosing a
public home, adding an exact target/footprint, and documenting the claim
boundary:

- `ReachableDrift`
- `ReachableDrift/Basic`
- `ReachableDrift/Diagnosis`
- `ReachableDrift/FloorBridge`

The family is green and overlap-audited, with a classifier, faithfulness and
separation results.  The only policy decision is whether the disclosed
`Classical.choice` footprint of `diagnosis_exhaustive` is acceptable.  If the
bundle is not wanted publicly, move all four to skunkworks; do not split it.

### Move canonical live ownership to skunkworks — 43

Break-glass incubation:

- `BreakGlassAuthorization`

Post-v10 application/reversal work:

- `AffectiveCouplingClassification`
- `BorrowedSpend`
- `CommitmentStanding`
- `RegulatorRecovery`
- `SelfEntrenchment`
- `SignalAuthority`
- `StatusConversionBinding`

Observer/plural-custody work:

- `AbsoluteForceStampBridgePrice`
- `BridgeInterfaces`
- `ConsumerRelativeForce`
- `ConsumerRelativeFreshness`
- `DeadlockEscalation`
- `DeadlockTrajectory`
- `MultiConsumerAdoption`
- `QuorumResidueCoupling`
- `ShardedCustody`

Temporal-price campaign:

- `AnticipatoryBridgePrice`
- `PostHocLegitimationBridgePrice`
- `RetroactiveBridgePrice`
- `TemporalTrajectory`

Runtime/identity/refusal contracts:

- `AuthenticatedDenial`
- `ControlPathIndependence`
- `ExecutionRevalidation`
- `FailureCustodyDisposition`
- `FencedEpochAuthority`
- `LinearSpendStanding`
- `NoFreeContinuation`
- `NoFreeStandingReadout`
- `ReplaySafeActionIdentity`
- `ResidueCustodyNoncollapse`
- `UncheckedResourceCertificate`
- `UncertaintyCustody`
- `VersionBoundAction`
- `WitnessContactMode`

Larger research/proof-of-encodability candidates:

- `AdmissibleIncompleteness`
- `AggregateWitnessRequiresJoin`
- `BestEffortCompleteness`
- `Labelwatch`
- `OperatorBasisGateInput`
- `Paper6TemporalClosureKernel`
- `ProvenanceProfiles`
- `SurfaceDeformationRequiresCoupling`

These are meaningful live investigations, not garbage.  They belong in the
place where names, assumptions, overlap, and hostile specimens may still
change without creating public surface gravity.

### Skunkworks-bound, pending a Mathlib incubation home — 2

- `ConsolidationController`
- `QuorumCustody`

Both are green but import Mathlib.  The current sibling skunkworks is explicitly
Mathlib-free.  Create a deliberate non-default Mathlib incubation island (or an
honest core-only refactor) before moving them; do not leave them public merely
because the destination is presently missing.

### Deprecate/delete from live source — 20

Findings already absorbed or exact supersessions:

- `Admissibility/BoundaryWitness`
- `Admissibility/GuardCollapse`
- `Scratch/AuthorityScope`
- `Scratch/PredicateWitnessSeparation`
- `AbstractNormalizationInstance`
- `TemporalCustody`
- `RetroactiveFigLeaf`
- `TemporalToSurfaceBridge`

Observer fossils subsumed by v10 determination:

- `ConsumerRelativeVerdict`
- `NoUniversalRoot`
- `ObserverPacket`

Frozen NQ snapshot:

- `NQJudgments`
- `NQJudgments/Basic`
- `NQJudgments/NoFreeLift`
- `NQJudgments/Standing`

Retired or superseded prototypes:

- `BoundaryTransit`
- `LogOnlyProvesEmission`
- `PersistenceAttractor`
- `SeamEdges`
- `SeamPathVerdicts`

Git/tag history is the provenance record.  If a live import is discovered,
use a clearly deprecated re-export for one transition rather than retaining a
false incubation class.

## BreakGlass return conditions

`BreakGlassAuthorization` is not a quick lift and should move to skunkworks
after `PathVerdict.Core` is rehomed publicly.  A later public return needs:

1. an end-to-end inhabited exceptional attempt → commit → settlement path,
   rather than only a settlement specimen starting from a constructed live
   obligation ledger;
2. hostile negative specimens for replay, wrong snapshot/actor/action/scope,
   revocation, duplicate nonce, missing receipt, and invalid default;
3. dead-surface removal or an explicit reason each remaining definition is
   public;
4. a decision on use-time re-derivation and multi-snapshot/re-issuance
   semantics;
5. an exact API and axiom-footprint gate; and
6. a stable-API versus public-evidence decision.

This is suitable for post-v12 incubation and probably its own later campaign,
not a v12 point release.

## Dependency-ordered migration

1. Record the new custody contract: skunkworks is the sole incubation lane;
   stable API and public evidence are separate terminal public roles.
2. Rehome and classify the 21-module v4-v7 closure.  Update skunkworks PC-0,
   the paid finite-support application, Lake targets, namespaces, and imports
   atomically.
3. Rehome `PathVerdict/Core` and `Edges`, then move BreakGlass to skunkworks.
4. Correct the ten-module Witnessed stable closure; optionally split its three
   fossils/specimen modules into a `WitnessedEvidence` target later.
5. Reclassify the v3 Bounded family, v12 examples, paid evidence, and finished
   Admissibility evidence.  Create exact evidence targets rather than widening
   `AdmissibilityKernels`.
6. Create public roots for Dynamic Trace and SafetyBridge; package or decline
   the ReachableDrift bundle.
7. Rehome ViewSemantics source evidence atomically with its application
   adapters and gates.
8. Move the 45 live incubations (43 ordinary plus two Mathlib-bound) with
   `v12.0.0` path/commit provenance.  Remove the 20 superseded/historical
   modules after repairing citations.
9. Replace the partial custody checker with a fail-closed whole-tree registry;
   add exact stable-root closure and exact evidence registries.  Public modules
   must not import skunkworks or a residual Scratch namespace.
10. Update live docs and target names.  Preserve historical release ledgers as
    dated truth; add a post-v12 classification note rather than rewriting
    their old custody statements.
11. Run the complete build/audit battery and sibling import/parity checks.

## Tooling and policy follow-up

- `AGENTS.md` currently says `AdmissibilityKernels.lean` is the sole stable
  promotion mechanism.  That is no longer factually complete: Witnessed,
  PaidRecomposition, and JudgmentOrientation have exact stable roots too.
- `scripts/check-custody-classes.sh` must scan every `LeanProofs/**/*.lean`
  module and require exactly one recognized class.  Exact surface registries
  remain separate gates; a global marker check cannot replace them.
- Rename/remove `AdmissibilityCustodyAnnex`, `CustodyIndexedSequents`, and
  application/annex comments according to the final stable/evidence roles.
- Keep Mathlib evidence in explicit island targets.
- **Superseded by the v13 continuation:** the 45
  `UNRATIFIED-CANDIDATE` modules were subsequently included in the same
  dependency-first audit.  Current dispositions are governed by the v13
  migration ledger rather than by this first-pass deferral.

## Verification receipt

The audit was read-only before this ledger was added.  Bare commands observed
with exit status 0:

```text
lake build BoundedCalculi Witnessed PaidRecompositionEvidence JudgmentOrientationExamples
lake build CustodyIndexedSequents ViewSemanticsApplications PaidRecompositionEvidence
bash scripts/check-custody-classes.sh
lake env lean <each of the 103 Scratch artifacts, individually>
```

The passing custody script is evidence that its registered subset is
internally consistent; it is not evidence of whole-tree enforcement.
