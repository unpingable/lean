# v12 Release Ledger — Judgment Orientation

> **Historical record.** This is the frozen v12 release inventory. v13 later
> reclassifies `Examples` as terminal public evidence rather than ANNEX; the
> exact five-module stable root and all theorem claims remain unchanged. See
> [`V13-RELEASE-LEDGER.md`](V13-RELEASE-LEDGER.md).

**Released: v12.0.0 — Judgment Orientation (2026-07-16).** This ledger records
the frozen claim, public surface, custody classification, and verification
receipt for the released tree.

Prior release: `v11.0.0` — Occurrence-Exact Paid Recomposition. A local
annotated v11 tag exists, with tag object
`d77ee38b9c50da715baff1e907c7becd07cc61d0` and peeled target
`7cf3a6afedf4f1f93ebdf677e0fdcafd331fa52c`. This local fact does not establish
external GitHub-release or Zenodo-deposit state.

Repository version metadata is `12.0.0` in `lakefile.toml`; `CITATION.cff`
carries the title `Judgment Orientation`, version `12.0.0`, release date
`2026-07-16`, and concept DOI `10.5281/zenodo.20369489`. The repository has no
`.zenodo.json`; no substitute file is created. A version-specific DOI exists
only if the separate Zenodo deposit completes, so it is not inferred from the
tag or GitHub release.

## Frozen release claim

> Raw custody is a sequence; effective exact-origin contribution is its
> finite-support join-semilattice projection.

The v12 family separates inquiry posture from protected judgment state,
localizes protected endpoint differences to privileged change points, retains
ordered raw occurrence custody while counting an exact origin once, and
composes those results one way: an endpoint-visible orientation-invariant
difference across an attributed trace names a privileged step whose
caller-supplied origin is contained in the effective support of the trace's
privileged provenance.

This is a sibling theorem family. It does not modify the stable 1.x
`AdmissibilityKernels` import list and is not a claim that a runtime conforms
to the formal model.

## Exact public surface and custody

The stable root is `LeanProofs.JudgmentOrientation`. Its complete direct import
list is:

```lean
import LeanProofs.JudgmentOrientation.Core
import LeanProofs.JudgmentOrientation.Attribution
import LeanProofs.JudgmentOrientation.Provenance
import LeanProofs.JudgmentOrientation.OriginSupport
import LeanProofs.JudgmentOrientation.Bridge
```

The exact source registry is:

| Module | Custody | Role |
| --- | --- | --- |
| `LeanProofs.JudgmentOrientation` | PUBLIC-SHIPPED | Exact stable aggregate root |
| `JudgmentOrientation.Core` | PUBLIC-SHIPPED | Inquiry/protected-state confinement |
| `JudgmentOrientation.Attribution` | PUBLIC-SHIPPED | Privileged change-point localization |
| `JudgmentOrientation.Provenance` | PUBLIC-SHIPPED | Ordered custody and exact-origin replay accounting |
| `JudgmentOrientation.OriginSupport` | PUBLIC-SHIPPED | Abstract finite-support join/order algebra and projections |
| `JudgmentOrientation.Bridge` | PUBLIC-SHIPPED | One-way protected-change to supported-origin composition |
| `JudgmentOrientation.Examples` | ANNEX | Streetlamp, laundering, relay, accumulator, payload-conflict, bridge, non-vacuity, and non-converse fixtures |

The stable target and ANNEX fixtures are separate Lake libraries. The stable
root imports no example, Scratch, or Mathlib module. `EffectiveSupport` keeps
its representation private; the public promise is its algebraic API and laws,
not a particular quotient carrier.

## Exact claims and nonclaims

The five public modules establish:

- pure-orientation traces preserve certification, probe authority, and action
  authority, while governed application requires separate admission evidence;
- endpoint-visible protected differences across mixed traces localize to a
  privileged step, without treating localization as justification and without
  claiming to detect later-reverted changes;
- replay remains visible in raw custody while exact-origin contribution is
  idempotent;
- finite support has bottom, join, membership, inclusion, partial-order and
  least-upper-bound laws, support cardinality, append-as-join, and streaming /
  batch projection agreement; and
- an attributed privileged step carries its occurrence structurally, allowing
  the one-way bridge without fabricating origin evidence.

V12 does **not** prove origin authentication or trusted issuance; Sybil or
common-cause independence; payload fidelity without an additional witness;
linear, one-shot, expiring, or revocable `MayOrient` evidence; admissibility,
safety, or approval of a privileged step; the converse from support to visible
change; or runtime/deployment conformance.

## Frozen footprint receipts

`scripts/check-judgment-orientation-footprint.sh` re-attests these thirteen
receipts exactly:

| Receipt | Exact footprint |
| --- | --- |
| `OrientationTrace.runRaw_protected` | none |
| `no_orientation_without_admission` | none |
| `Attribution.change_localizes_to_privileged` | `propext`, `Classical.choice`, `Quot.sound` |
| `Provenance.duplicate_does_not_raise_heat` | `propext` |
| `Provenance.run_replayed_batch_accounting_idempotent` | `propext`, `Classical.choice`, `Quot.sound` |
| `Provenance.originFaithful_run_decomposed_iff` | `propext` |
| `OriginSupport.EffectiveSupport.join_assoc` | `propext`, `Quot.sound` |
| `OriginSupport.EffectiveSupport.join_le_iff` | `propext`, `Quot.sound` |
| `OriginSupport.EffectiveSupport.ofTrace_append` | `propext`, `Quot.sound` |
| `OriginSupport.EffectiveSupport.ofState_run` | `propext`, `Quot.sound` |
| `OriginSupport.EffectiveSupport.replayed_custody_strictly_grows` | `propext` |
| `Bridge.changed_protected_has_supported_privileged_origin` | `propext`, `Classical.choice`, `Quot.sound` |
| `Bridge.certification_change_has_supported_privileged_origin` | `propext`, `Classical.choice`, `Quot.sound` |

The disclosed family maximum is therefore exactly
`[propext, Classical.choice, Quot.sound]`. Missing or renamed receipts,
`sorryAx`, or footprint drift fail closed.

## Inherited v11 custody and gate corrections

V12 records two hygiene corrections, neither of which changes a theorem,
definition, import, or capability:

1. The v11 paid stable graph already had an exact eight-module closure. The
   unchanged `NoFreeLift` → `Derivation` → `Sequent` → `ResourceSequent` →
   `ResourceChecker` foundation is reclassified from legacy ANNEX/SCHEMA
   headers to `PUBLIC-SHIPPED`, matching the public `Payment` API's existing
   dependency on `ResourceChecker.removeAt`. Together with the paid root,
   `Payment`, and `Catalog`, all eight stable modules are now enforced public;
   the three paid evidence modules remain ANNEX. The corrected gate freezes
   all 15 foundation types/definitions, all 18 constructors, both scoped
   notations, and all 45 public foundation theorems; 30 of those theorems are
   axiom-free and 15 use exactly `propext`.
2. The direct Scratch exception for
   `Applications.FiniteSupportOneCrossing` is enforced as the exact singleton
   `LeanProofs.Scratch.FiniteSupportChecker`. Missing, duplicate, replaced, or
   additional direct Scratch imports fail, including additional modules on the
   same import command. Its intended transitive Scratch closure remains
   allowed behind that one direct edge.

The tagged v11 tree is not rewritten. Its dated readiness ledger carries a
post-release addendum distinguishing the historical headers from the corrected
v12 custody registry.

## Deferred Scratch campaign

`LeanProofs/Scratch/BreakGlassAuthorization.lean` is tracked, compiles directly,
and is Mathlib-free, but remains SCRATCH, unwired, and outside every v12 claim,
target, receipt set, and custody promotion. V12 neither edits nor silently
admits it. Before a later regression target or ANNEX decision, it still needs
dead-surface cleanup, an explicit end-to-end exceptional-path inhabitation
specimen, a focused API/axiom gate, and removal or reclassification of its
SCRATCH `PathVerdict.Core` dependency.

## Verification receipt

The commands and checks below were run directly from the repository root on
the released v12 tree. The recorded values are their bare exit statuses, never
piped or visually inferred statuses:

| Command | Exit |
| --- | ---: |
| `lake build` | 0 |
| `lake build Witnessed` | 0 |
| `lake build PaidRecompositionEvidence` | 0 |
| `lake build JudgmentOrientation JudgmentOrientationExamples` | 0 |
| `lake build LeanProofs AdmissibilityMathlibIslands` | 0 |
| `lake build ViewSemantics ViewSemanticsApplications ViewSemanticsMathlibIslands` | 0 |
| `bash scripts/check-witnessed-footprint.sh` | 0 |
| `bash scripts/check-paid-recomposition-footprint.sh` | 0 |
| `bash scripts/check-judgment-orientation-footprint.sh` | 0 |
| `bash scripts/check-viewsemantics-footprint.sh` | 0 |
| `bash scripts/check-viewsemantics-isolation.sh` | 0 |
| `bash scripts/audit-axioms.sh` | 0 |
| `bash scripts/audit-native-decide.sh` | 0 |
| `bash scripts/check-mathlib-pin.sh` | 0 |
| `bash scripts/check-custody-classes.sh` | 0 |
| `bash scripts/check-mathlib-free-targets.sh` | 0 |
| `lake env lean LeanProofs/Scratch/BreakGlassAuthorization.lean` | 0 |
| BreakGlass tracked / byte-unchanged / unwired check | 0 |
| repository Lean proof-hole scan | 0 |
| paid direct-Scratch negative fixtures | 0 |
| CFF YAML/title/version/date/DOI and lake-version agreement | 0 |
| `git diff --check` | 0 |

## Release record

The `v12.0.0` tag and associated
[GitHub release](https://github.com/unpingable/lean/releases/tag/v12.0.0)
archive this exact verified tree. As checked 2026-07-20, the Zenodo concept's
public version history contains no v12 record. No v12 version DOI is therefore
claimed here; repairing or minting that external record remains an operator
action.

Publication changes no custody class, import boundary, API, theorem, or proof
footprint, and it proves no runtime conformance.
