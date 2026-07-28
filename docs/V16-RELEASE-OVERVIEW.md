# V16 — Governed Transition Boundaries

> **Start here.** Release orientation: what shipped, what it does and does not
> establish, and how to verify it.

**Status: released 2026-07-28.**

Subtitle: **Which selected targets factor through which source views.**

v16 adds one public-evidence surface. It asks a single question in a
mechanically checked form: given a target and a view of the source, is there
*one total decoder* that recovers the target from the view, correctly for
every source? Four generic theorems answer the structural half, and one
declared-finite calculation plus five bounded witnesses answer instances of
it.

The version DOI is minted by the GitHub release creation and recorded from
Zenodo afterward, never guessed here. The concept DOI
`10.5281/zenodo.20369489` identifies the series and does not move.

## What is proved

**Generic core** (`LeanProofs.GovernedTransitionBoundaries`, four axiom-free
receipts). `ExplicitlyFactorsThrough view target` holds when one total decoder
is correct for every source. Such factorizations compose; they imply the
existing public `ViewSemantics.Determines` fibre-constancy relation; a
target-distinguishing collision blocks them; and a carrier obtained solely by
deterministic postprocessing of an insufficient view does not restore them.

The converse is not proved and is not true in general: for arbitrary types,
fibre constancy does not construct representatives of reachable view fibres or
values for unreachable view outputs. Quotient and coequalizer settings, and a
surjective view with a section, are positive controls only when that
additional lifting data is actually present.

**Declared finite representation** (`…Evidence/FiniteRepresentation.lean`). In
a declared seven-coordinate language, with a declared source list of length
1,024 covering every `AnalysisCase` and 128 duplicate-free coordinate
selections: `internalMinimum` is the unique least selection determining the
selected five-component target in the declared
`AtlasSelection.Includes` order; exactly two masks in the enumeration
determine that target, with membership, count, and duplicate freedom proved;
the declared six-field carrier explicitly factors the five-target result; and
no declared selection factors the modeled hidden relation or the combined
six-target result.

This is functional dependency in a fixed table and a fixed coordinate
language. It is not statistical sufficiency, arbitrary-carrier minimality, or
a canonical global semantics.

**Five bounded witnesses.** Each is scoped to its own fixture and claims
nothing beyond it.

| Witness | What it shows | What it is not |
| --- | --- | --- |
| Fixed-policy authorization refusal | One product computes its target while one fixed grant-list policy refuses inspection and reliance | A general authorization theory |
| Selected-context validation | One issued observation record does not factor the validation target across two use contexts | A temporal, expiration, revocation, or certificate-lifecycle result |
| Bounded capacity realizability | Per-pair support records revalidate at the empty prefix while the three-event execution type is uninhabited | General amalgamation, CSP consistency, or schedulability |
| Occurrence-link observation | Two worlds share a present-state view and differ on one occurrence-link Boolean | Causality, proof of occurrence, or a hyperproperty |
| Modeled hidden-relation nonidentifiability | Two worlds agree at the admitted acquisition interface and differ on one hidden Boolean | Physical truth, attestation correctness, or causal identification |

The constructors in the context-validation fixture carry no temporal or prefix
order. "Transition-relative computation" is a bounded program label for the
observation that some targets factor through views carrying transition or
history context when they do not factor through a coarser projection; it
defines no operational semantics.

## What is not new

The generic statements are standard function-factorization and
view-determinacy facts, and the finite result is an exhaustive
functional-dependency and attribute-selection calculation. The contribution is
their mechanically checked synthesis with the five separately scoped
witnesses. **No novelty or priority is claimed.** The nearest established
structures are named in the
[`public index`](V16-PUBLIC-INDEX.md#prior-art-anchors), with the closest
being the database distinction between view determinacy and rewriting.

## Relation to v15

v15 is a Cross-Calculus Atlas of selected, receipt-indexed correspondences
that preserves native indices and receipts without selecting a shared bridge
algebra. Its `ATLAS` classification and its four negative results —
`FRONTIER-NOT-COMPOSITIONAL`, `NO-USEFUL-OWNERSHIP-COMMONALITY`,
`CONTEXT-TRANSPORT-NOT-GENERIC`, `ONLY-DOMAIN-SPECIFIC-RESIDUAL-THEORIES` —
are unchanged and remain authoritative.

v16 asks a different question: which selected targets uniformly factor through
which views. It neither replaces the v15 bridge surfaces nor promotes a shared
cross-calculus semantics. No existing public module depends on it; its core
and evidence are separately rooted.

## Custody position

v16 promotes no stable surface. The ten new sources are `PUBLIC-EVIDENCE`
under two new registered targets; `scripts/stable-surfaces.tsv` and every
registered stable root's import list are unchanged from v15. The sources are
byte-pinned: the crossing gate reproduces each public SHA-256 and Git blob and
re-derives the extracted body by removing exactly the twelve-line custody
block.

| | v16 | v15 |
| --- | ---: | ---: |
| public Lean sources | 283 | 273 |
| stable / evidence / aggregate | 115 / 167 / 1 | 115 / 157 / 1 |
| stable roots / ownerships | 12 / 142 | 12 / 142 |
| registered targets | 30 | 28 |
| new receipts | 29 | — |

## Verification

The repository pins Lean 4.29.0 (`leanprover/lean4:v4.29.0`). Pass/fail is the
exit code of the bare command.

```bash
lake build GovernedTransitionBoundaries GovernedTransitionBoundariesEvidence
bash scripts/check-governed-transition-boundaries-crossing.sh
bash scripts/check-governed-transition-boundaries-footprint.sh
```

The footprint gate replays all 29 receipts: 16 axiom-free, 7 `[propext]`, 6
`[propext, Quot.sound]`, zero `Classical.choice`, zero `sorryAx`. The full
battery and per-gate results are in
[`V16-READINESS-LEDGER.md`](V16-READINESS-LEDGER.md).

## Navigation

Ordered from orientation to exact accounting. Stop wherever your question is
answered.

1. **This document** — what shipped and why.
2. [`V16-GOVERNED-TRANSITION-BOUNDARIES.md`](V16-GOVERNED-TRANSITION-BOUNDARIES.md)
   — exact per-witness fences and the reference list.
3. [`V16-PUBLIC-INDEX.md`](V16-PUBLIC-INDEX.md) — module map, prior-art
   anchors, and the complete non-claim ledger.
4. [`V16-RELEASE-LEDGER.md`](V16-RELEASE-LEDGER.md) — release identity and
   frozen accounting.
5. [`V16-READINESS-LEDGER.md`](V16-READINESS-LEDGER.md) — source pins, axiom
   accounting, and the qualification commands.

Reference:
[`V16-PUBLIC-SOURCE-CROSSING-RECEIPT_2026-07-26.md`](V16-PUBLIC-SOURCE-CROSSING-RECEIPT_2026-07-26.md)
— per-file digest table, frozen at the pre-release state.
