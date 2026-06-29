# Lean Repo Audit - 2026-06-29

## Executive summary

The canonical Lean build is healthy, but the custody registry is not fully
coherent with the current tree.

- `lake build` succeeds.
- `lake build Witnessed` succeeds.
- `bash scripts/check-witnessed-footprint.sh` succeeds and re-attests the
  Witnessed calculus footprint.
- `bash scripts/check-custody-classes.sh` fails because
  `LeanProofs/Admissibility/README.md` still states 51 files and ANNEX 25, while
  the live tally is 53 files and ANNEX 27.
- No live Lean proof hole from `sorry`/tactic `admit` was found. Several
  intentionally documented axioms, `True` placeholders, and marker theorems
  remain important non-doctrine boundaries.

No scratch was promoted during this audit. The only pre-existing working-tree
change before this report was a scratch comment addition in
`LeanProofs/Scratch/QuorumCustody.lean`.

## Current build status

Pre-change status observed before writing this report:

```text
$ git status --short
 M LeanProofs/Scratch/QuorumCustody.lean

$ git diff --stat
 LeanProofs/Scratch/QuorumCustody.lean | 5 +++++
 1 file changed, 5 insertions(+)
```

Build/check commands run:

```text
$ lake build
Build completed successfully (8324 jobs).
```

Observed replay included `LeanProofs.Admissibility.DeferredWitness`,
`LeanProofs.Admissibility.PredicateWitnessSeparation`,
`LeanProofs.Admissibility.AuthorityScope`, and `LeanProofs.Witnessed.Examples`.

```text
$ lake build Witnessed
Build completed successfully (16 jobs).
```

```text
$ bash scripts/check-witnessed-footprint.sh
OK: Witnessed builds Mathlib-free; 10 ratified receipts within attested footprint
    6 axiom-free, 2 x [propext], 2 x [propext, Quot.sound]
```

```text
$ bash scripts/check-custody-classes.sh
FAIL: README states ANNEX = 25 but live tally is 27
FAIL: README states 51 total .lean files but live count is 53
  (README count drift - reconcile prose against this script's tally)
```

Direct checks of the two drift-explaining ANNEX files:

```text
$ lake build LeanProofs.Admissibility.AuthorityScope
Build completed successfully (2 jobs).

$ lake build LeanProofs.Admissibility.PredicateWitnessSeparation
Build completed successfully (2 jobs).
```

Sandbox note: some read-only `sed`, `rg`, and shell-script commands initially
failed under the sandbox wrapper with `bwrap: loopback: Failed RTM_NEWADDR:
Operation not permitted`. They were rerun with read-only escalation where needed.
That wrapper failure is not a Lean build failure.

## Module and import map

Lake configuration:

- Root package: `lean_proofs`, version `1.4.0`.
- Default targets: `LeanProofs`, `Witnessed`.
- `LeanProofs` library: canonical root `LeanProofs.lean`, which imports the
  root specimen modules, root-wired Admissibility modules, `CollapsedSurface`,
  and the Witnessed aggregator.
- `Witnessed` library: separate `lean_lib`, `srcDir = "."`,
  `roots = ["LeanProofs.Witnessed"]`, and globs for `LeanProofs.Witnessed.+`.
  This is the build-graph fence for the Mathlib-free witnessed calculus.
- `experiments/no_free_lift_wiring/`: separate Lake project and toolchain;
  non-canonical tracked wiring witness.

Inventory counts observed:

- `LeanProofs/**/*.lean`: 118 files.
- `LeanProofs/Admissibility/*.lean`: 53 files.
- `LeanProofs/Witnessed/*.lean`: 13 files.
- `LeanProofs/Scratch/**/*.lean`: 41 files.
- `experiments/no_free_lift_wiring/**/*.lean`: 23 files.

Root `LeanProofs.lean` import shape:

- Root specimens: `Basic`, `TaxonomyGraph`, `PersistenceModel`,
  `BranchSelector`, `RepairOperator`, `OpsMasking`, `Paper24SharedVision`,
  `Paper25EpistemicBorderControl`, `CollapsedSurface`.
- Admissibility root-wired set: 37 imports total, consisting of the 35 intended
  public/annex/deprecated Admissibility imports plus the two newer ANNEX imports
  `AuthorityScope` and `PredicateWitnessSeparation`.
- Witnessed: imported via `LeanProofs.Witnessed`, whose separate library also
  owns `LeanProofs.Witnessed.Examples` by glob.

Admissibility public surface:

- `LeanProofs.Admissibility.AdmissibilityKernels` imports exactly the 8
  `PUBLIC-SHIPPED` modules: `Authority`, `StateTransition`, `Derivation`,
  `Execution`, `Corrective`, `Freshness`, `SurfaceAuthorization`,
  `WitnessInvariance`.
- `CalculusOne` remains a `DEPRECATED` shim imported by root for compatibility.
- Promotion is by aggregator membership, not by compilation or marker text.

Admissibility files not imported by `LeanProofs.lean`:

```text
AmendmentFragment
BoundaryWitness
BudgetMerge
CarryLaws
Conductance
ConsequencePartition
ContractionHinge
GuardCollapse
Mandamus
MergeConflict
NoFreeLift
NoFreeStandingBridge
ParameterizedMerge
ProjectionLaundering
RetroactiveLegitimation
StaleEvidenceMerge
```

These match the fenced `UNRATIFIED-CANDIDATE` / `SCRATCH` bucket. They are not
default-regression doctrine. Build them directly only when auditing that fenced
material.

Other non-canonical Lean files:

- Root-level sketches outside the canonical library path:
  `taxonomy-lean-sketch.lean`,
  `non-reciprocal-admissibility-flow-sketch.lean`.
- `LeanProofs/Admissibility.lean`: P27 obligation skeleton, intentionally not
  root-wired.
- `LeanProofs/Scratch/**`: first-class exploratory Lean. Some scratch files have
  internal aggregators/imports (`NQJudgments`, `ReachableDrift`,
  `ObserverPacket`), but they remain fenced scratch.

## Scratch/promoted boundary observations

The repo already has a strong custody vocabulary:

- `PUBLIC-SHIPPED`: public compatibility surface.
- `ANNEX`: compiled support, regression-covered, not public surface.
- `UNRATIFIED-CANDIDATE`: named candidate, not root-wired.
- `SCRATCH`: exploratory, may clarify shape and test non-collapse, but may not
  testify, discharge doctrine, authorize code, or silently promote.
- `DEPRECATED`: compatibility shim.

Boundary is mostly coherent:

- `LeanProofs/Scratch/` is a first-class home for fenced exploratory Lean.
- `experiments/` is explicitly non-canonical wiring witness territory.
- `LeanProofs.Witnessed.*` is a canonical public surface, but its ratified
  experiment source remains preserved under `experiments/no_free_lift_wiring/`
  as provenance, not as an import path.
- `AdmissibilityKernels` remains the promotion gate for public admissibility
  modules.

Boundary drift found:

- `AuthorityScope` and `PredicateWitnessSeparation` have been promoted from
  scratch to ANNEX and are root-imported, but registry prose still says 51
  Admissibility files and ANNEX 25. Live count is 53 files and ANNEX 27.
- `AdmissibilityKernels.lean` still enumerates ANNEX as 13 kernel-adjacent plus
  11 consumer specimens. Its own custody note says changes to annex enumeration
  require explicit ratification, so this report does not silently patch it.
- `LeanProofs/Admissibility/README.md` has the same count drift. Some later prose
  says counts were reconciled, but the live script proves they drifted again.

## Wiring gaps

SAFE_WIRING candidates:

- Record the current custody-count drift in this report.
- Treat `AuthorityScope` and `PredicateWitnessSeparation` as live ANNEX modules
  needing registry reconciliation, not theorem work.
- Add a future docs-only reconciliation slice after operator approval, because
  the aggregator says annex enumeration changes require ratification.

PROMOTION_CANDIDATE items:

- `AuthorityScope`: already ANNEX, useful scoped-conversion receipt wall; any
  promotion beyond ANNEX requires explicit operator review.
- `PredicateWitnessSeparation`: already ANNEX, useful projection-vs-witness wall;
  introduction rules remain prose debt and must not be inferred from the Lean
  payload.
- Witnessed frontier register items: normalization as an admitting-class theorem,
  cut-elimination, non-suppression, reachability classification, and
  receiver-facing refusal legibility/propagation. These are named-not-started or
  post-release frontiers, not audit patches.

SCRATCH_EXPANSION items:

- `QuorumCustody`, `ShardedCustody`, `TemporalCustody`, `TemporalTrajectory`,
  `ConsumerRelative*`, `MultiConsumerAdoption`, `NQJudgments`,
  `ReachableDrift`, and `ObserverPacket` are active scratch neighborhoods. They
  can be expanded only as fenced exploration.
- The pre-existing `QuorumCustody` edit is consistent with scratch discipline:
  it clarifies a synchronic/diachronic boundary and does not promote doctrine.

DO_NOT_TOUCH items:

- Do not wire `LeanProofs/Admissibility.lean` into root. It is an intentionally
  unwired P27 skeleton with `True` placeholders.
- Do not wire the 16 fenced Admissibility files into root without a promotion
  receipt.
- Do not treat root-level sketch files as canonical modules without adding an
  explicit custody story first.
- Do not fold `experiments/no_free_lift_wiring` into canonical imports. Its job
  is provenance/integration witness.
- Do not fix the custody-count failure by changing class markers. The markers
  are already valid; the failure is registry prose drift.

## Placeholder and proof-boundary audit

No live proof hole was found by token sweep. `sorry` occurrences are comments or
historical notes; `admit` occurrences are mostly ordinary vocabulary or
constructors/fields named `admit`.

Important non-doctrine boundaries:

- `LeanProofs/TaxonomyGraph.lean` has `axiom persistence_normalizes : ... True`.
  It is intentionally weak and marks the static/dynamic boundary. It must not be
  cited as a theorem that persistence dynamics are proved.
- `LeanProofs/Admissibility.lean` has two `True` placeholder theorems:
  `masked_recovery_not_resolved` and `orphaned_causality_inadmissible`.
  This file is intentionally unwired.
- `LeanProofs/Admissibility/StateTransition.lean`,
  `Derivation.lean`, and `Freshness.lean` use abstract `axiom Type` / opaque
  operations as interface commitments. These are not runtime schemas.
- `LeanProofs/Admissibility/AuthorizedNotSafe.lean` is axiomatic by design and
  is paired with concrete witness modules. Cite the paired discharge when making
  consistency claims.
- `kernels_compile` and `calculus_one_compiles` are marker theorems of type
  `True`; they certify build reachability only, not doctrine.

Potential semantic weakness to keep fenced:

- Any theorem whose conclusion is `True`, or whose model uses constant
  `fun _ => True`/`fun _ _ => True`, must be read in local context. Some are
  deliberate nontriviality tests or degenerate countermodels; none should be
  promoted into substantive claims without a nearby fence.
- `PredicateWitnessSeparation` deliberately strips introduction rules from its
  witness payload. That is a strength of the separation result and a hard limit:
  it proves projection underdetermination, not a predicate-witness doctrine.

## Docs/spec concepts not yet represented in Lean

- `docs/WITNESSED-FRONTIER-REGISTER.md` names several future directions not
  implemented as canonical Lean: admitting-class normalization, cut-elimination,
  non-suppression, reachability-based composition classification, refusal
  legibility/propagation, and witnessed clocks/temporal custody.
- `PAPER-MAP.md` names P23 cases (ii) and (iii), P24 conjectural/dynamic parts,
  P25 quantitative substitution scaling and closed-loop dynamics, and broader
  dynamic-roadmap items as intentionally not Leaned.
- `CLAIM-REGISTER.md` still carries prose-level fixes and open/stale claims; it
  is an audit register, not a theorem source.
- `experiments/no_free_lift_wiring/ATLAS-MAP.md` is explicitly a candidate
  correspondence to another repo, not a verified bridge from this repo.

## Expansion candidates

| Candidate | Classification | Reason |
| --- | --- | --- |
| Custody count reconciliation in README/aggregator prose | PROMOTION_CANDIDATE | Docs-only in content, but aggregator says annex enumeration changes require ratification. |
| Add audit report | SAFE_WIRING | Records observed facts without altering doctrine. |
| `AuthorityScope` registry placement | PROMOTION_CANDIDATE | Already ANNEX and root-wired; further registry update should be operator-gated. |
| `PredicateWitnessSeparation` registry placement | PROMOTION_CANDIDATE | Already ANNEX and root-wired; introduction-rule debt must stay explicit. |
| P27 skeleton wiring | DO_NOT_TOUCH | Intentionally unwired and has `True` placeholders. |
| 16 fenced Admissibility files | DO_NOT_TOUCH | Current status is unratified/scratch; direct builds only, no root import. |
| Scratch receiver/quorum/temporal work | SCRATCH_EXPANSION | Useful exploration, but compile-is-contact only. |
| Witnessed frontier work | PROMOTION_CANDIDATE | Real future theorem work, but requires forcing case and operator review. |
| Root-level sketch files | DO_NOT_TOUCH | Outside canonical module tree and lack current custody/wiring story. |
| Experiment tree wiring | DO_NOT_TOUCH | Non-canonical provenance/integration witness by design. |

## Recommended first 3 slices

1. Audit artifact only: land this report and keep the current Lean source
   untouched.
2. Operator-gated docs reconciliation: update
   `LeanProofs/Admissibility/README.md` and, if ratified, the ANNEX enumeration
   in `AdmissibilityKernels.lean` to account for `AuthorityScope` and
   `PredicateWitnessSeparation`. No theorem changes.
3. Fenced scratch inventory: add or refresh scratch index documentation that
   groups `QuorumCustody`, temporal custody, consumer-relative, NQ, and
   ReachableDrift scratch by theme and repeats compile-is-contact/non-authority
   rules. No root imports.

## Do not promote without operator review

- Any `LeanProofs/Scratch/**` file.
- Any `UNRATIFIED-CANDIDATE` module under `LeanProofs/Admissibility/`.
- `LeanProofs/Admissibility.lean` P27 skeleton.
- Any theorem currently expressed as `True` placeholder, marker theorem, or
  degenerate-model specimen.
- Any model-to-world transfer claim.
- Any Witnessed frontier item.
- Any experimental wiring result under `experiments/`.
- Any docs-to-Lean inference where the doc names doctrine but Lean only supplies
  shape, countermodel, or compile contact.

## Safe immediate next slice

Create/keep this report as the audit artifact. No Lean source, import, Lake, or
custody-marker changes are needed for the safe immediate slice.

## Operator-gated next slice

Ratify and apply the custody registry reconciliation for the two new ANNEX
modules: `AuthorityScope` and `PredicateWitnessSeparation`. Expected work is
documentation/enumeration only, but it crosses an explicit ratification sentence
in `AdmissibilityKernels.lean`.

## Risky / defer

Defer scratch promotion, P27 wiring, Witnessed frontier theorem work,
experiment-to-canonical wiring, and any model-to-world transfer theorem. Those
are authority-sensitive and should not be bundled with this audit.
