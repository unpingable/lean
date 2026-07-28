# v16 Release Ledger — Governed Transition Boundaries

> **Read this if** you need the release identity and the frozen numbers:
> admission commits and trees, custody and target counts, and the axiom
> footprint partition.

**Released: v16.0.0 — Governed Transition Boundaries (2026-07-28).** Baseline:
`v15.0.0` (`69bdc032dc00db1e750ffc6fdc9f73a8cdcbbf81`, tree
`b102a07968e10461694a50adc9d5864e1c7bfa2c`, 2026-07-24). Repository version
metadata is `16.0.0` in `lakefile.toml`; `CITATION.cff` carries the title
`Governed Transition Boundaries`, version `16.0.0`, release date
`2026-07-28`, and concept DOI `10.5281/zenodo.20369489`. The version DOI is
minted by the GitHub release creation and recorded from Zenodo afterward,
never guessed here.

## Scope

v16 admits one new public-evidence surface: a generic explicit-factorization
core and a bounded evidence surface answering, for selected targets and
selected source views, whether a single total decoder factors the target
through the view.

Four generic core theorems state that explicit factorizations compose, imply
the existing public `ViewSemantics.Determines` fibre-constancy relation, are
blocked by a target-distinguishing collision, and are not restored by
deterministic postprocessing of an insufficient view. Twenty-five evidence
receipts carry one declared-finite coordinate-determinacy calculation and five
separately scoped witnesses.

v16 promotes no stable surface. The registered stable roots, their import
lists, and `scripts/stable-surfaces.tsv` are unchanged from v15. The new
surface is `PUBLIC-EVIDENCE` under two new registered targets, and no existing
public module depends on it.

## Admission history (frozen)

| Step | Content | Commit | Tree |
| ---: | --- | --- | --- |
| 1 | Generic explicit-factorization core | `3ced60c6dd14aa50aa182c3669b08679116d77f2` | `5e4f7635fd256e41ba9dd71efc021dcb82ec1f5d` |
| 2 | Declared-finite representation and five bounded witnesses | `09bd81ed44b2f94d73541329954481583b94d465` | `15c004f1074e9d7735a9186df784898623610776` |
| 3 | Candidate scope, non-claims, and prior-art anchors | `31c19e333e3d986f2245ee3bb706e9108ee0e7c2` | `db0eb855e679df6f8d6cad8c9335d20510ca62a3` |
| 4 | Custody rows, target rows, CI step, footprint gate | `160a97ffb17ae3c7cd1f69ffce61268ee17074ef` | `0ce29743a1a4c3e70fef5f98c958ae600c04c1ff` |
| 5 | Source-crossing receipt and crossing gate | `65405f180a9a254686b2c0e59b57b168a4f84024` | `075b4976a6b0a40f14de164326e4dc32a1313842` |

Each step's parent is the preceding row; step 1's parent is the v15 tag
commit. The release-positioning commit that carries this ledger is recorded in
[`V16-READINESS-LEDGER.md`](V16-READINESS-LEDGER.md), which is committed
alongside it; a commit cannot contain its own object ID.

## Frozen public accounting

- **Custody**: 283 public Lean sources — 115 STABLE-SURFACE, 167
  PUBLIC-EVIDENCE, 1 REPOSITORY-AGGREGATE — across twelve exact stable roots
  and 142 ownership relations (v15 baseline: 273/115/157/1, twelve roots,
  142). Stable count, root count, and ownership count are unchanged; the ten
  new sources are entirely public evidence.
- **Targets**: 283/283 public sources target-owned across 30 registered
  targets in two Lake projects, 690 local target/module ownerships (v15
  baseline: 273/273, 28 targets).
- **Governed-transition-boundaries footprint**: 29 exact receipts — 4 in the
  core root, 25 in the evidence root — fail-closed in
  `scripts/check-governed-transition-boundaries-footprint.sh`.
- **Source crossing**: 10 public destinations byte-pinned in
  `scripts/check-governed-transition-boundaries-crossing.sh` by public
  SHA-256, public Git blob, and extracted-body SHA-256 after removal of the
  exact twelve-line custody block. The per-file digest table is
  [`V16-PUBLIC-SOURCE-CROSSING-RECEIPT_2026-07-26.md`](V16-PUBLIC-SOURCE-CROSSING-RECEIPT_2026-07-26.md).
- **Aggregate**: `LeanProofs.lean` imports both new roots. Per `AGENTS.md`,
  an aggregate import is regression coverage and is not a promotion.

## Axiom footprint partition

Disjoint, gate-derived over the 29 receipts:

| Footprint | Receipts |
| --- | ---: |
| axiom-free | 16 |
| `[propext]` | 7 |
| `[propext, Quot.sound]` | 6 |
| `[Classical.choice]` | 0 |
| `sorryAx` | 0 |

The gate fails closed on any `sorryAx` or `Classical.choice` dependency. The
ten sources additionally contain no `sorry`, `admit`, custom `axiom` or
`constant`, `unsafe`, `native_decide`, or private campaign import.

## What v16 does not claim

The generic statements are standard function-factorization and
view-determinacy facts, and the finite result is an exhaustive
functional-dependency and attribute-selection calculation in one declared
seven-coordinate language. The contribution is their mechanically checked
synthesis with five separately scoped witnesses. No novelty or priority is
claimed.

The converse of the core factorization result is not claimed: fibre constancy
does not construct decoders for arbitrary types. Each of the five witnesses is
bounded to its own fixture, and "transition-relative computation" is a bounded
program label, not an operational semantics. The per-witness fences are in
[`V16-GOVERNED-TRANSITION-BOUNDARIES.md`](V16-GOVERNED-TRANSITION-BOUNDARIES.md);
the complete non-claim ledger is in
[`V16-PUBLIC-INDEX.md`](V16-PUBLIC-INDEX.md#explicitly-unearned).

Lean alone establishes no runtime conformance. A runtime claiming
correspondence to v16 must declare its exact scope, supply an explicit map for
every governed distinction in that scope, and provide executable preservation
and transport evidence with revision-bound qualification receipts. The full
evidence contract is in
[`../WHAT-THIS-PROVES.md`](../WHAT-THIS-PROVES.md#formal-contract-and-runtime-conformance).

The v15 classification is unchanged and remains authoritative for the Atlas
surface: `FRONTIER-NOT-COMPOSITIONAL`, `NO-USEFUL-OWNERSHIP-COMMONALITY`,
`CONTEXT-TRANSPORT-NOT-GENERIC`, `ONLY-DOMAIN-SPECIFIC-RESIDUAL-THEORIES`,
final classification `ATLAS`. v16 neither replaces the v15 bridge surfaces nor
promotes a shared cross-calculus semantics.

## Verification receipt (release-positioning tree)

All by bare exit code, 2026-07-28, after the version metadata flip and
documentation sync. The full command list and per-gate results are in
[`V16-READINESS-LEDGER.md`](V16-READINESS-LEDGER.md).

- full battery per `AGENTS.md` — every build target, every footprint gate
  (incl. 29/29 governed-transition-boundaries, 191/191 Calculus, 36/36
  PathVerdict, 13/13 JudgmentOrientation), the 10-source crossing gate, axiom
  and native_decide audits, Mathlib pin and closure, custody (283/115/167/1,
  twelve roots, 142), target gate (283/283, 30 targets), V15 continuity
  rename, V15 integration, release qualification, downstream consumer — pass
- the release-qualification gate was split at v16: the V15 campaign checker
  asserted that release's metadata literals and diffed changed paths against a
  frozen allowlist, so any later release makes it false by construction. Its
  durable half — metadata consistency, registered claim invariants, and the
  declaration-footprint census — is now `scripts/check-release-qualification.py`,
  and the per-release data it needs lives in `scripts/release-invariants.tsv`
  and `scripts/post-transfer-admissions.tsv`
- the transfer freeze in `check-v15-integration.py` was narrowed from every
  path under `LeanProofs/` to `LeanProofs/*.lean`. It had reported
  "existing public source calculus drift" for the v16 currency edit to
  `LeanProofs/Admissibility/README.md`; the freeze protects unpinned public
  Lean sources, which is what `AGENTS.md` already documented it as covering
- the three checkers pinned to earlier commits
  (`check-v15-public-qualification.py`, `check-v15-public-transfer.py`,
  `check-gt-c03-admission.py`) do not pass at this tree by construction, as
  recorded in `AGENTS.md`; none is a regression
- tag, GitHub release, and Zenodo deposit are separate operator acts that
  follow this tree and change no theorem, custody class, import boundary, or
  footprint

---

Previous: [`V16-PUBLIC-INDEX.md`](V16-PUBLIC-INDEX.md) — module map and
complete non-claim ledger. Next:
[`V16-READINESS-LEDGER.md`](V16-READINESS-LEDGER.md) — source pins, axiom
accounting, and the qualification commands.
