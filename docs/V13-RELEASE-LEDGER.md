# v13 Release Ledger — Repository Custody Migration

**Released: v13.0.0 — Repository Custody Migration (2026-07-16).** Baseline:
`v12.0.0` (`b528af8`, 2026-07-16). This ledger records the frozen custody
boundary, source accounting, compatibility classification, and verification
receipt for the released tree.

Repository version metadata is `13.0.0` in `lakefile.toml`; `CITATION.cff`
carries the title `Repository Custody Migration`, version `13.0.0`, release
date `2026-07-16`, and concept DOI `10.5281/zenodo.20369489`. The repository
has no `.zenodo.json`; no substitute file is created. Zenodo assigns the
version-specific DOI externally when the GitHub release drives the deposit,
so that DOI is intentionally not guessed or hard-coded here.

## Scope

v13 is a repository-custody correction, not a mathematical campaign.  The
theorem and definition bodies being rehomed are intended to remain unchanged.
The compatibility boundary comes from module paths and namespaces, public
roots and evidence targets, import/parity manifests, and the enforcement
contract itself.

The migration is deliberately narrow:

1. give every live Lean module exactly one honest terminal disposition;
2. distinguish compatibility-bearing stable API from terminal public
   evidence;
3. make the sibling skunkworks the sole live incubation lane;
4. remove superseded source whose only remaining provenance is Git history;
5. replace partial marker checking with fail-closed whole-tree enforcement;
   and
6. repair paths, roots, targets, imports, parity records, and current docs.

No theorem generalization, opportunistic API redesign, or new campaign is in
scope unless a move is mechanically impossible without it.

## Why a major boundary is honest

The post-v12 sweep began with the 244 modules under `LeanProofs/`, but the
full tracked-source audit found **271 Lean files** at the v12 baseline.  The
old custody checker examined only **84 of those 244 `LeanProofs` modules** and
accepted a tree in which 36 modules lacked an exact recognized marker.  Its
green result attested consistency inside a partial registry; it did not
classify the repository.

The follow-up audit of the 108 candidate or previously unmarked modules found
24 stable-API modules, 44 terminal public-evidence modules, 11 skunkworks
incubations, and 29 historical/superseded modules.  Combined with the original
ANNEX/Scratch sweep, this exposed the real problem: `ANNEX`, `Scratch/`, and
`UNRATIFIED-CANDIDATE` had become sedimentary locations rather than meaningful
lifecycle states.

Because the correction changes import paths, namespaces, build targets, and
the mechanically enforced public closure, it is a v13 compatibility boundary
even though it adds no mathematical claim.

## Terminal custody model

The public repository has three repository roles, expressed under the single
public custody class:

| Header | Meaning |
| --- | --- |
| `Custody-Class: PUBLIC-SHIPPED` + `Surface-Role: STABLE-SURFACE` | Compatibility-bearing definitions and theorems reachable from a registered exact stable root. |
| `Custody-Class: PUBLIC-SHIPPED` + `Surface-Role: PUBLIC-EVIDENCE` | Finished examples, countermodels, specimens, applications, and audit fossils. Public and citable, but not imported into a stable root and not an API promise. |
| `Custody-Class: PUBLIC-SHIPPED` + `Surface-Role: REPOSITORY-AGGREGATE` | A build/contact aggregate, not itself a theorem-family promotion mechanism. |

Live incubation is not a fourth public-repository role.  It belongs in the
sibling skunkworks, where names, assumptions, hostile specimens, and overlap
may still change.  A green build remains mathematical attestation; wiring is
regression coverage; neither action changes custody.  A tag or DOI archives a
tree and likewise does not perform promotion.

`PUBLIC-EVIDENCE` is terminal.  A finished countermodel or release specimen
does not need to become compatibility-bearing API to remain public, and it
must not be mislabeled as unfinished merely because it is excluded from a
stable root.

## Corrective public rehomes

The v13 release recognizes existing released dependency truth; it does
not introduce new capability.

- The v4-v7 checker/sequent substrate moves unchanged from
  `LeanProofs/Scratch/` to `LeanProofs/CustodyIndexed/`, with stable root
  `LeanProofs.CustodyIndexed` and terminal evidence under
  `LeanProofs.CustodyIndexed.Evidence`.  The released calculus and v11 paid
  evidence already depended on this foundation.
- `PathVerdict.Core` and `PathVerdict.Edges` move to
  `LeanProofs/Admissibility/PathVerdict/` behind the stable
  `LeanProofs.Admissibility.PathVerdict` root.  The obstruction and coverage
  fixtures live under its evidence root.
- Finished ViewSemantics applications move under
  `LeanProofs/ViewSemantics/Evidence/`; the Mathlib-reaching P25 adapter stays
  in an explicit evidence island.
- Witnessed, ProofTheory, JudgmentOrientation, PaidRecomposition, Bounded
  Calculi, DynamicTrace, SafetyBridge, ReachableDrift, and the remaining
  Admissibility families receive explicit stable/evidence ownership rather
  than inheriting status from directory folklore.

The Bounded Calculi split follows the corrected v4 stable import closure, not
a new ranking of the v3 family.  `BoundaryArtifact` is imported by the stable
`BridgeCompositionSequent` and `TemporalToSurfaceBridgeWiring` modules, and
the latter also imports `SafetyPreservation`; their disclosed surrogate
boundary records and toy safety specimen are therefore accepted as part of
that unchanged module-level compatibility substrate.  `CheckpointSettlement`
and `RefusalDenial` remain terminal public evidence because no registered
stable root imports either module.  Avoiding the first result would require
splitting or reworking released bridge modules, or shrinking the corrected v4
stable root; promoting the latter pair would require new stable roots or
imports. None of those changes is a content-neutral custody correction, so
v13 performs none of them.

These are corrective reclassifications of already-compiled material.  v13
must not describe them as new v13 mathematics.

## Skunkworks transfer and historical deletion

The complete sweep identified **53 live incubations** for transfer to the
sibling skunkworks.  Four are Mathlib-bound
(`LocalBoundary`, `LocalBoundaryPressure`, `ConsolidationController`, and
`QuorumCustody`) and require a deliberate, non-default Mathlib incubation
island there; all four now live in that island rather than remaining falsely
public.

The transfer is complete: **53 of 53** live incubations now have canonical
skunkworks homes and pass the sibling's 26-check migration audit. This includes
all 45 former `LeanProofs/Scratch/` leaves, `RefusalPropagation`,
`LocalBoundary`, and the six final returns listed below. All public duplicates
have been removed.

| Deleted public source | Canonical skunkworks return |
| --- | --- |
| `LeanProofs/Admissibility.lean` | `formalization/Calculi/Scratch/P27ObligationSkeleton.lean` |
| `LeanProofs/Admissibility/Conductance.lean` | `formalization/Calculi/Scratch/Conductance.lean` |
| `LeanProofs/Admissibility/LocalBoundaryPressure.lean` | `formalization/MathlibIncubation/Skunkworks/MathlibIncubation/LocalBoundaryPressure.lean` |
| `LeanProofs/Admissibility/Mandamus.lean` | `formalization/Calculi/Scratch/Mandamus.lean` |
| `LeanProofs/Admissibility/ParameterizedMerge.lean` | `formalization/Calculi/Scratch/ParameterizedMerge.lean` |
| `non-reciprocal-admissibility-flow-sketch.lean` | `formalization/Calculi/Scratch/NonReciprocalAdmissibilityFlowSketch.lean` |

Accordingly, the released public tree contains exactly 179 Lean modules.

Twenty Scratch/Admissibility fossils were classified for deletion or
deprecation after citation repair.  The separate obsolete
`experiments/no_free_lift_wiring` Lean project is also retired: its
ratification prose remains as historical provenance while the superseded
source is recoverable from v12 and Git history.

The full-tree audit also records these four deletions explicitly; none is a
new theorem removal from a registered stable root:

| Deleted v12 source | v13 disposition |
| --- | --- |
| `LeanProofs/Admissibility/CarryLaws.lean` | Superseded namespace duplicate of the canonical stable `LeanProofs/Witnessed/CarryLaws.lean`; delete the duplicate rather than maintain two authorities. |
| `LeanProofs/Admissibility/NoFreeLift.lean` | Superseded namespace duplicate of the canonical stable `LeanProofs/Witnessed/NoFreeLift.lean`; delete the duplicate rather than maintain two authorities. |
| `LeanProofs/Basic.lean` | Obsolete Lake scaffold containing only `def hello := "world"`; no theorem-family or evidence role. |
| `taxonomy-lean-sketch.lean` | Historical standalone taxonomy probe superseded by `LeanProofs/TaxonomyGraph.lean`; not a second public surface. |

All four exact v12 files remain recoverable from the v12 tag and Git history.
The custody correction deletes redundant or historical source; it does not
rewrite the archived release.

The final source-integrity audit accounts for all **138** removed v12 paths:
38 corrective public rehomes, 53 skunkworks transfers, 23 retired experiment
sources, 20 previously classified fossils, and the four explicit deletions
above. There are zero unaccounted removals. Of the 179 retained public modules,
171 retained/rehomed theorem sources are token-equivalent to v12 and eight are
new import-only roots; the migration adds no theorem body.

No public module or manifest imports the old Scratch namespace. Transfer,
verification, and operator review are complete.

## BreakGlass disposition

`BreakGlassAuthorization` is a real campaign, not clerical promotion.  A
later public return needs all of the following:

1. an inhabited exceptional attempt → commit → settlement path, rather than
   only a settlement specimen beginning from a constructed live obligation;
2. hostile negative specimens for replay, wrong snapshot/actor/action/scope,
   revocation, duplicate nonce, missing receipt, and invalid default;
3. removal of dead definitions or a stated public purpose for each;
4. a decision on use-time re-derivation and multi-snapshot/re-issuance
   semantics;
5. an exact API and axiom-footprint gate; and
6. an explicit stable-API versus public-evidence decision.

That work is post-v13 mathematical incubation.  It is not part of this
custody-only release boundary and is not presumed to be a v12 point release.

## Fail-closed release condition

The release is not attested merely because all files compile. The whole-tree
custody gate must enumerate the entire existing tracked-or-untracked Lean tree
and fail on:

- a missing, duplicate, or unrecognized custody/role header;
- a source path absent from the public custody registry;
- any residual `LeanProofs/Scratch` path or import;
- a stable root whose transitive closure contains public evidence;
- a registered stable module outside its declared exact root closure.

The separate public-target gate must fail on an exact evidence/stable target
that absorbs a role outside its declaration, an owned source missing from its
manifest, any public source with no role-compatible registered target owner,
or Mathlib reaching a target declared Mathlib-free.

Build targets, footprint gates, axiom/native-decision classifiers, and sibling
parity checks remain independent receipts.  Whole-tree custody enforcement
does not replace them.

## Verification receipt

All independent public-repository build, theorem-footprint, axiom,
`native_decide`, Mathlib-pin/isolation, and diff gates pass in this release
receipt.
All 53 returned incubations pass the sibling's 26-check skunkworks migration
audit, including sibling imports and PathVerdict parity.

The fail-closed whole-tree gate passes the actual public tree with exactly
**179 `PUBLIC-SHIPPED` Lean files** — 82 stable, 96 public evidence, and one
repository aggregate — across ten registered stable roots and 98
root-ownership relations. The strengthened public-target gate separately
passes across two repository-owned Lake projects with 23 public targets and
23 exact local closures, 19 Mathlib-free current-tree targets, 463 local
target/module ownerships, one pinned-external target, and one locked external
boundary. Its reverse check gives all 179/179 public sources a role-compatible
registered target owner. The nested downstream fixture's bare build completes
19 jobs.

The final integrated rerun is earned: the complete public suite passes on the
post-transfer tree; a clean temporary-copy sibling build completes 149 jobs;
the Mathlib incubation aggregate and all four member modules pass; and the
sibling's full `formalization_audit.py ci` passes 29 checks. Operator review
accepted this exact boundary for release.

## Completion checklist

- [x] Audit the full v12 source tree, including candidate/unmarked modules.
- [x] Define stable API, public evidence, and repository aggregate roles.
- [x] Rehome the v4-v7 and PathVerdict public families in the release tree.
- [x] Separate stable roots from evidence roots for the major public families.
- [x] Identify fossils and remove superseded Lean source in the release tree.
- [x] Transfer all 53 live incubations to skunkworks with provenance.
- [x] Complete all four Mathlib-bound transfers in the explicit skunkworks
  island.
- [x] Repair sibling imports and PathVerdict parity manifests.
- [x] Land fail-closed whole-tree custody enforcement and pass its exact
  179-file final shape on the actual tree.
- [x] Pass the strengthened target gate over its exact closure, Mathlib,
  ownership manifests, and reverse-complete 179/179 source coverage.
- [x] Pass the independent build, footprint, axiom, native-decision, Mathlib,
  and diff gates for the release receipt.
- [x] Re-run the entire battery, including sibling/parity and whole-tree
  custody, on the final post-transfer tree.
- [x] Complete operator review of the final tree.

## Release record

The `v13.0.0` tag and associated GitHub release archive this exact verified
tree. GitHub release creation drives the corresponding Zenodo version deposit
and version DOI beneath concept DOI `10.5281/zenodo.20369489`; the
version-specific DOI is assigned externally and is therefore not hard-coded
in this source tree.

Publication changes no custody class, import boundary, API, theorem, or proof
footprint, and it proves no runtime conformance.

## Historical-record policy

The dated v3-v12 release ledgers describe the custody labels and paths that
existed in those archived trees.  v13 does not silently rewrite them.  Where a
current reader could otherwise mistake an old `ANNEX`, `SCRATCH`, or
`UNRATIFIED-CANDIDATE` label for present custody, the ledger receives an
explicit post-v12 correction note pointing here.  Git tags remain the exact
historical artifacts; this migration records the later classification
correction.
