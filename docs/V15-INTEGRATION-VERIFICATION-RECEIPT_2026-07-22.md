# V15 public integration verification receipt

Date: 2026-07-22

Disposition: `READY-FOR-V15-INTEGRATION-RATIFICATION`

The ratified public transfer is integrated behind canonical, non-default
public-evidence targets. `Someone` has crossed to `Continuity.Admission` with
its declaration, proof-value, and axiom correspondence preserved. StaticRole
remains closed at R3. PJ remains exactly `ATLAS`: a faithful cross-calculus
atlas, not a shared algebra or universal calculus.

No push, tag, mint, publication, release, remote configuration, remote-branch
change, stable-root promotion, default-target change, or release-metadata
change occurred.

## Transfer base

- transfer commit: `d1e2d18ffc6e27365ec890a6ae2439c87688b350`
- transfer tree: `fbd5a31ec5e2432759db45d2359c3e3f74198b52`
- transfer parent: `9dca58f4587a4a4f5b724662b176af8de3040c04`
- transfer-manifest SHA-256:
  `05a29867a8c9c24996f9a1b975749a61379f32b5b8cdebc9a1100504147d6268`
- normalized custody manifest SHA-256:
  `471ec4b52bdcb163dafa8eab671e5f26b9401351ff4da9908db0ab8e214b5e1d`

The transfer object is an ancestor of this receipt. Its tree, frozen campaign
manifests, final-verdict record, and existing public `LeanProofs` source
calculi reproduce exactly.

## Integration commits and exact paths

### 1. Transfer ratification

- commit: `8bfa849693b3795b6c7236161baaa54c9f1f82f2`
- tree: `d47f0f779d05031e8ae61937cfb1e1b5e03800e2`
- parent: `d1e2d18ffc6e27365ec890a6ae2439c87688b350`
- path: `docs/V15-PUBLIC-TRANSFER-OPERATOR-RATIFICATION_2026-07-22.md`

### 2. Exact Continuity rename

- commit: `46e7a9aa5944fcc8826445c74ec08e1aa2dcb630`
- tree: `e27bc3174d3e9bd2d6f843d871a823c2b036674b`
- parent: `8bfa849693b3795b6c7236161baaa54c9f1f82f2`
- correspondence SHA-256:
  `3aafc4eceb0e96899772bb5824bbac3c999ede5e9355786982e3761a2071fabb`
- paths:
  - `docs/V15-CONTINUITY-ADMISSION-CORRESPONDENCE.tsv`
  - `docs/V15-CONTINUITY-ADMISSION-HISTORICAL-NOTE.md`
  - `someone/Someone.lean` to `formalization/Continuity/Admission.lean`
  - `formalization/ContinuityQualification.lean` to
    `formalization/Continuity/Admission/Qualification.lean`
  - `formalization/ContinuityQualification/Core.lean` to
    `formalization/Continuity/Admission/Qualification/Core.lean`
  - `formalization/ContinuityQualification/Hostile.lean` to
    `formalization/Continuity/Admission/Qualification/Hostile.lean`
  - `formalization/ContinuityQualification/Campaign/Qualification.lean` to
    `formalization/Continuity/Admission/Qualification/Campaign.lean`
  - `formalization/PJ/Instances/SomeoneContinuity.lean` to
    `formalization/PJ/Instances/ContinuityAdmission.lean`
  - `formalization/scripts/SomeoneContinuityDeclarationDump.lean` to
    `formalization/scripts/ContinuityAdmissionDeclarationDump.lean`
  - `formalization/PJ.lean`
  - `formalization/PJ/Campaign/TrancheAQualification.lean`
  - `formalization/PJ/Campaign/TrancheBPrimeQualification.lean`
  - `formalization/PJ/Campaign/TrancheCPrimeQualification.lean`
  - `formalization/PJ/TrancheBPrime/Instances.lean`
  - `formalization/PJ/TrancheCPrime/ContextTransport.lean`
  - `formalization/PJ/TrancheCPrime/Ownership.lean`
  - `formalization/scripts/PJTrancheADeclarationDump.lean`
  - `formalization/scripts/PJTrancheBPrimeDeclarationDump.lean`
  - `formalization/scripts/PJTrancheCPrimeDeclarationDump.lean`
  - `formalization/scripts/PJTrancheDPrimeDeclarationDump.lean`
  - `lakefile.toml`
  - `scripts/check-v15-continuity-rename.py`
  - `scripts/public-custody.tsv`
  - `scripts/public-targets.tsv`

The correspondence covers 1,005 declarations: fully qualified names, kinds,
normalized theorem/type expressions, proof values, and axiom footprints.
There is no duplicate authoritative `Someone` implementation.

### 3. Formal dependency integration

- commit: `0b513fa184c12a10c685a6d13e45d085cd19499b`
- tree: `39ddfae2d420961cbe4809abe1ed1c3a4073e112`
- parent: `46e7a9aa5944fcc8826445c74ec08e1aa2dcb630`
- paths:
  - `docs/V15-FORMAL-INTEGRATION.md`
  - `formalization/PJ.lean`
  - `lakefile.toml`
  - `scripts/public-targets.tsv`

The canonical targets are `V15Integration` and
`V15IntegrationQualification`. They are explicit, Mathlib-free,
public-evidence targets and are not stable or release aggregates.

### 4. Track A reconciliation

- commit: `05b4dff4df27bf69a9e3552498bc2ef92bed3242`
- tree: `8b2ebf8d9a8b715ce932e61d52e173f0d9f6f900`
- parent: `0b513fa184c12a10c685a6d13e45d085cd19499b`
- path: `docs/V15-TRACK-A-ATLAS-RECONCILIATION.md`
- record SHA-256:
  `ac9a182a68aac28452cc1ebf3dba7ae71f7eeac4b565cc2fc9509b71f383d9ac`

The private Track A freeze remains commit
`cfeffc950e795752ad1928a314890185c0cda723`, tree
`4d9de55c0d19f3984dc486ac124b2e4f2a7e1e11`. Its six Lean blobs and
three boundary-record blobs reproduce exactly. Inquiry and Preparation are
independent comparison-only neighbors outside the frozen PJ primary surface.

### 5. Cleanup and public index

- commit: `76d568a78d1611420ea765901ae679a9bc16ee84`
- tree: `3167a74fe0c08a24e14c8de5d87ff9a01f413201`
- parent: `05b4dff4df27bf69a9e3552498bc2ef92bed3242`
- paths:
  - `docs/V15-PUBLIC-INDEX.md`
  - `lakefile.toml`
  - `scripts/public-targets.tsv`
- index SHA-256:
  `3deba9369ca2ae679b6cd39a8c478f8386dd78b600a1053fa4e384db7b464aba`

The two temporary transfer targets were removed only after their canonical
replacements were green. All transferred formal sources remain owned.

### Exact namespace-terminator correction

- commit: `8113544cd7e8420d14b3f02c2325873aef2ac15b`
- tree: `68ba6198a56d66c81592fdef882b2f9ff805c037`
- parent: `76d568a78d1611420ea765901ae679a9bc16ee84`
- path: `formalization/PJ/Instances/ContinuityAdmission.lean`

The full source-identity checker found that the renamed adapter had relied on
Lean's end-of-file namespace closure rather than retaining its explicit final
`end` line. This commit restores that exact namespace-adjusted terminator.
The module built before and after; its declaration, theorem, proof-value, and
axiom surfaces are identical. The correction is isolated rather than hidden
in cleanup or history rewriting.

## Manifest and verdict verification

The five frozen declaration-manifest SHA-256 digests are:

| Manifest | SHA-256 |
| --- | --- |
| Continuity historical declaration manifest | `521c437be1d7f2ac93d0dfded7b368158a339cad8ee004ffb29d41120848c3b9` |
| PJ-A | `be2b092ed2e08e948858e7d7a6ae77893b1baf36b6d95cb58050401cfbe2955a` |
| PJ-B-prime | `c7544b561271ca64f0c15d8f7c9a980b7cf7eb3da8ce020f0aece3c3aebfebc4` |
| PJ-C-prime | `09c203d95157afb0ef379668f64753a9e74fb22c7e2387c8efde7c5e5d4821ab` |
| PJ-D-prime | `5b4947101d4610fa86c536449e4eba399b601cf4c1b3cb396579d668b39f6e6a` |

The integrated checker verifies all four PJ dumps against their frozen
manifests after only the authorized namespace correspondence: 1,950
cumulative manifest declarations, including 74 cumulative axiom-bearing
entries. Source text for every declaration-bearing renamed PJ file is the
exact transfer source after the authorized rename substitutions. Unchanged
public source calculi remain byte-identical to the transfer base.

The final PJ operator-verdict record remains SHA-256
`3efad909f66b2caed45e57606c3c879ad877e902606d4046e057eff7942002aa`
and says `RATIFY-PJ-D: ATLAS`. It retains:

- `FRONTIER-NOT-COMPOSITIONAL`;
- `NO-USEFUL-OWNERSHIP-COMMONALITY`;
- `CONTEXT-TRANSPORT-NOT-GENERIC`; and
- `ONLY-DOMAIN-SPECIFIC-RESIDUAL-THEORIES`.

No rejected PJ frontier directory and no StaticRole R4 path exists.

## Verification commands

Each bare command below exited zero in the indicated repository:

```text
/home/jbeck/git/lean$ lake build V15Integration
/home/jbeck/git/lean$ lake build V15IntegrationQualification
/home/jbeck/git/skunkworks/formalization$ lake build CalculiStable CalculiScratch CalculiAll Calculi
/home/jbeck/git/skunkworks/formalization$ python3 scripts/formalization_audit.py check --skip-external --skip-footprints
/home/jbeck/git/lean$ lake env lean formalization/Continuity/Admission/Qualification/Campaign.lean
/home/jbeck/git/lean$ lake env lean formalization/StaticRole/Campaign/Qualification.lean
/home/jbeck/git/lean$ lake env lean formalization/StaticRole/Campaign/PhaseThreeQualification.lean
/home/jbeck/git/lean$ lake env lean formalization/PJ/Campaign/TrancheAQualification.lean
/home/jbeck/git/lean$ lake env lean formalization/PJ/Campaign/TrancheBPrimeQualification.lean
/home/jbeck/git/lean$ lake env lean formalization/PJ/Campaign/TrancheCPrimeQualification.lean
/home/jbeck/git/lean$ lake env lean formalization/PJ/Campaign/TrancheDPrimeQualification.lean
/home/jbeck/git/lean$ python3 scripts/check-v15-continuity-rename.py
/home/jbeck/git/lean$ python3 scripts/check-v15-integration.py
/home/jbeck/git/lean$ bash scripts/check-custody-classes.sh
/home/jbeck/git/lean$ bash scripts/check-mathlib-free-targets.sh
/home/jbeck/git/lean$ git diff --check
```

The Calculi build completed 269 jobs. The formalization audit passed 19
checks. The custody gate closed over 273/273 public Lean sources, and the
target gate closed over 28 registered public targets with 273/273 public
sources target-owned. Every changed path was inspected.

This receipt's commit and tree are recorded in the operator-facing handoff;
they cannot be embedded in the receipt without making its Git object
self-referential. Its exact parent is
`8113544cd7e8420d14b3f02c2325873aef2ac15b`, and its only paths are this
receipt and `scripts/check-v15-integration.py`.
