# V16 readiness ledger — Governed Transition Boundaries

Date: 2026-07-27

Status: **released 2026-07-27**

v16 admits a generic explicit-factorization core and a bounded evidence
surface answering, for selected targets and selected source views, whether one
total decoder factors the target through the view. It promotes no stable
surface, changes no registered stable root or import list, and adds no
dependency to any existing public module.

This ledger is rooted at the source-crossing qualification commit
`65405f180a9a254686b2c0e59b57b168a4f84024`, tree
`075b4976a6b0a40f14de164326e4dc32a1313842`, parent
`160a97ffb17ae3c7cd1f69ffce61268ee17074ef`. The release-positioning commit
that carries this ledger, the version flip, the documentation sync, and the
release-gate split is its child; its object ID is recorded by the tag, not
here.

## Local chain

| Step | Commit | Tree | Parent |
| --- | --- | --- | --- |
| generic factorization core | `3ced60c6dd14aa50aa182c3669b08679116d77f2` | `5e4f7635fd256e41ba9dd71efc021dcb82ec1f5d` | `69bdc032dc00db1e750ffc6fdc9f73a8cdcbbf81` |
| bounded evidence surface | `09bd81ed44b2f94d73541329954481583b94d465` | `15c004f1074e9d7735a9186df784898623610776` | `3ced60c6dd14aa50aa182c3669b08679116d77f2` |
| candidate scope record | `31c19e333e3d986f2245ee3bb706e9108ee0e7c2` | `db0eb855e679df6f8d6cad8c9335d20510ca62a3` | `09bd81ed44b2f94d73541329954481583b94d465` |
| custody, targets, CI, footprint gate | `160a97ffb17ae3c7cd1f69ffce61268ee17074ef` | `0ce29743a1a4c3e70fef5f98c958ae600c04c1ff` | `31c19e333e3d986f2245ee3bb706e9108ee0e7c2` |
| source-crossing receipt and gate | `65405f180a9a254686b2c0e59b57b168a4f84024` | `075b4976a6b0a40f14de164326e4dc32a1313842` | `160a97ffb17ae3c7cd1f69ffce61268ee17074ef` |

Baseline: `v15.0.0`, annotated tag object
`b03f072027f57491b4b67d59592f0a0ac3c2d22f`, peeled commit
`69bdc032dc00db1e750ffc6fdc9f73a8cdcbbf81`, tree
`b102a07968e10461694a50adc9d5864e1c7bfa2c`, concept DOI
`10.5281/zenodo.20369489`.

## Source pins

- Private source repository: `unpingable/skunkworks`, commit
  `b3d73a7a8f3c47486a29767b8b28c809af0f4e57`.
- Extracted `LeanProofs` tree: `84f209f57e2495463833137cd58aac7ce73e6f96`.
- Extracted source snapshot pin: `f7b32f61cfd11b9bb6cafd1cf3674ddebface558`.
- Extraction path prefix:
  `formalization/PromotionCandidates/V16GovernedTransitionBoundaries/Extracted/LeanProofs/`.
- Crossing campaign date: `2026-07-26`.

Per-file public SHA-256, public Git blob, and extracted-body SHA-256 for all
ten destinations are tabulated in
[`V16-PUBLIC-SOURCE-CROSSING-RECEIPT_2026-07-26.md`](V16-PUBLIC-SOURCE-CROSSING-RECEIPT_2026-07-26.md)
and re-derived by `scripts/check-governed-transition-boundaries-crossing.sh`.
That receipt is frozen at the pre-release state and is not re-toned here.

## Source accounting

Ten public-evidence sources, 1,701 lines including custody blocks.

| Module | Theorem surface | Lines |
| --- | --- | ---: |
| `GovernedTransitionBoundaries.lean` | `GENERIC-CORE-AGGREGATE` | 18 |
| `GovernedTransitionBoundaries/Core.lean` | `GENERIC-EXPLICIT-FACTORIZATION-CORE` | 101 |
| `GovernedTransitionBoundariesEvidence.lean` | `BOUNDED-EVIDENCE-AGGREGATE` | 20 |
| `…Evidence/FiniteRepresentation.lean` | `DECLARED-FINITE-COORDINATE-DETERMINACY` | 864 |
| `…Evidence/JurisdictionBoundary.lean` | `FIXED-POLICY-AUTHORIZATION-REFUSAL-WITNESS` | 135 |
| `…Evidence/ContextBoundary.lean` | `SELECTED-CONTEXT-VALIDATION-WITNESS` | 139 |
| `…Evidence/RealizabilityBoundary.lean` | `BOUNDED-CAPACITY-REALIZABILITY-WITNESS` | 124 |
| `…Evidence/HistoricalBoundary.lean` | `OCCURRENCE-LINK-OBSERVATION-WITNESS` | 85 |
| `…Evidence/GroundingBoundary.lean` | `MODELED-HIDDEN-RELATION-NONIDENTIFIABILITY-WITNESS` | 126 |
| `…Evidence/Qualification.lean` | `SIGNATURE-AND-AXIOM-FOOTPRINT-GATE` | 89 |

Source-level declaration counts across the ten files: 50 `theorem`/`lemma`,
98 `def`/`abbrev`/`instance`, 52 `inductive`/`structure`. Of the 50 theorems,
**29 are the named receipt surface** re-checked by signature and axiom
footprint in `Qualification.lean` and by the external footprint gate; the
remaining 21 are supporting lemmas carried by their modules and not
individually pinned.

## Compiled receipt and axiom footprint

`scripts/check-governed-transition-boundaries-footprint.sh` replays all 29
receipts through `#print axioms` in the canonical build context and fails
closed on drift.

| Root | Receipts | Axiom-free | `[propext]` | `[propext, Quot.sound]` |
| --- | ---: | ---: | ---: | ---: |
| `GovernedTransitionBoundaries` (core) | 4 | 4 | 0 | 0 |
| `GovernedTransitionBoundariesEvidence` | 25 | 12 | 7 | 6 |
| **Total** | **29** | **16** | **7** | **6** |

Zero `[Classical.choice]` and zero `sorryAx` across the surface; both are
explicit fail-closed conditions in the gate. The normalized bodies contain no
`sorry`, `admit`, custom `axiom` or `constant`, `unsafe`, `native_decide`, or
private campaign import.

The four core receipts are axiom-free. All six `[propext, Quot.sound]` entries
are in the declared finite representation: `declared_analysis_atlas_covers`,
`selected_internal_exact_iff_includes_declared_minimum`,
`selected_internal_declared_minimum_is_least`,
`selected_internal_declared_least_is_unique`,
`selected_internal_mask_membership_iff_exact`, and
`selected_internal_exact_mask_classification`. The footprints are whatever the
compiler reports for the extracted proofs; this ledger records them and does
not claim anything about why each proof needs what it needs.

## Custody, target, and build accounting

| Gate | v16 | v15 baseline |
| --- | --- | --- |
| public Lean sources | 283 | 273 |
| STABLE-SURFACE | 115 | 115 |
| PUBLIC-EVIDENCE | 167 | 157 |
| REPOSITORY-AGGREGATE | 1 | 1 |
| stable roots | 12 | 12 |
| stable ownerships | 142 | 142 |
| registered targets | 30 | 28 |
| target-owned sources | 283/283 | 273/273 |
| local target/module ownerships | 690 | — |

`scripts/stable-surfaces.tsv` is unchanged. The ten new rows in
`scripts/public-custody.tsv` are all `PUBLIC-EVIDENCE` with no stable-root
owner; the two new rows in `scripts/public-targets.tsv` register
`GovernedTransitionBoundaries` and `GovernedTransitionBoundariesEvidence` as
`public-evidence`, `mathlib-free`, `default` targets. `LeanProofs.lean`
imports both roots for regression coverage, which per `AGENTS.md` is not a
promotion.

## Qualification commands

All run bare; pass/fail is the exit code.

```text
lake build
lake build Witnessed WitnessedEvidence
lake build CustodyIndexed CustodyIndexedEvidence
lake build PathVerdict PathVerdictEvidence
lake build JudgmentOrientation JudgmentOrientationEvidence
lake build ViewSemantics ViewSemanticsEvidence
lake build AdmissibilityEvidenceMathlib ViewSemanticsEvidenceMathlib
lake build GovernedTransitionBoundaries GovernedTransitionBoundariesEvidence
(cd downstream/wdc-v2-consumer && lake build)
bash scripts/check-witnessed-footprint.sh
bash scripts/check-paid-recomposition-footprint.sh
bash scripts/check-judgment-orientation-footprint.sh
bash scripts/check-pathverdict-footprint.sh
bash scripts/check-calculus-footprint.sh
bash scripts/check-viewsemantics-footprint.sh
bash scripts/check-viewsemantics-isolation.sh
bash scripts/check-governed-transition-boundaries-crossing.sh
bash scripts/check-governed-transition-boundaries-footprint.sh
bash scripts/audit-axioms.sh
bash scripts/audit-native-decide.sh
bash scripts/check-mathlib-pin.sh
bash scripts/check-custody-classes.sh
bash scripts/check-mathlib-free-targets.sh
python3 scripts/check-v15-continuity-rename.py
python3 scripts/check-v15-integration.py
python3 scripts/check-release-qualification.py
git diff --check
```

`check-v15-public-qualification.py`, `check-v15-public-transfer.py`, and
`check-gt-c03-admission.py` remain pinned to earlier commits and do not pass
at this tree by construction; `AGENTS.md` records why. None is a regression
and none was repinned. The first was retired at v16: it asserted the V15
release literals and diffed changed paths against a frozen allowlist, both of
which any later release makes false. Its live successor is
`check-release-qualification.py`, which keeps metadata consistency, registered
claim invariants, and the declaration-footprint census without pinning to a
release.

## Exact non-claims

The generic core is standard function factorization and view determinacy in a
witnessed total-decoder formulation; the finite result is an exhaustive
functional-dependency and attribute-selection calculation in one declared
seven-coordinate language. No novelty or priority is claimed. No converse of
the factorization result is claimed.

v16 establishes no new generic factorization theorem, Hennessy–Milner
characterization, statistical minimal sufficiency, general authorization
theory, temporal validity, general amalgamation, causal attribution,
attestation correctness, universal six-way independence, universal
transition-relative semantics, canonical global carrier, target-independent
least representation, arbitrary-carrier minimality, cross-surface composition,
runtime conformance, or product readiness.

The v15 `ATLAS` classification and its four negative results remain
authoritative and unchanged. v16 neither replaces the v15 bridge surfaces nor
promotes a shared cross-calculus semantics.
