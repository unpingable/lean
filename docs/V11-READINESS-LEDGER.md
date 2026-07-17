# v11 Readiness Ledger — Occurrence-Exact Paid Recomposition

> **Historical record.** ANNEX/Scratch labels and paths below describe the v11
> review. v13 makes all three fixtures public evidence and rehomes their
> finite-support foundation under `LeanProofs/CustodyIndexed/`; the v11 stable
> claim is unchanged. See [`V13-MIGRATION-LEDGER.md`](V13-MIGRATION-LEDGER.md).

**Historical status: RELEASE-READY / OPERATOR ACTIONS REMAIN (2026-07-15).**
At the time of this receipt, version and citation metadata were prepared as
`11.0.0`, and every V11-C post-wiring gate below exited zero. The ledger itself
created no git tag, GitHub release, Zenodo deposit, or DOI.

## Post-release custody correction (2026-07-16)

A local annotated `v11.0.0` tag now exists: tag object
`d77ee38b9c50da715baff1e907c7becd07cc61d0`, peeled commit
`7cf3a6afedf4f1f93ebdf677e0fdcafd331fa52c`. This is a local repository fact
only. External GitHub-release and Zenodo-deposit status were not verified and
are not asserted here.

The tagged v11 stable paid-recomposition graph already had the exact
eight-module closure recorded later in this ledger. `Payment` depended on
`ResourceChecker.removeAt`, and the closure continued through
`ResourceChecker`, `ResourceSequent`, `Sequent`, `Derivation`, and
`NoFreeLift`. The first four foundation files still carried legacy ANNEX
headers, while `NoFreeLift` carried the older `SCHEMA` label. The v12 tree
corrects those five headers to exact `Custody-Class: PUBLIC-SHIPPED` and makes
the paid/custody gates enforce all eight stable modules as public. Lean
declarations, theorem statements, proofs, and imports in the foundation are
unchanged. This repairs custody classification of the v11 closure; it is not
new v12 mathematics or capability and does not rewrite the tagged tree.

The v12 tree also closes one enforcement gap in the v11 paid gate. The tagged
gate required one direct import of
`LeanProofs.Scratch.FiniteSupportChecker` from the finite-support ANNEX, but
did not reject an additional direct `LeanProofs.Scratch.*` import. The
corrected rule requires the complete direct Scratch-import set to equal that
singleton, including when several modules share one import command.

Prior release: `v10.0.0` — View Semantics and Bounded Projection. The annotated
local v10 tag exists, with tag object `d174c9c` and peeled target `20b8da5`.
This local fact does not establish external GitHub release or Zenodo state and
does not rewrite v10 history.

In the tagged v11 tree, repository version metadata is `11.0.0` in
`lakefile.toml`; `CITATION.cff` carries the frozen v11 title, version, date,
abstract, and concept DOI. As in v9/v10, that tree has no `.zenodo.json`; no
substitute file was created.

## Frozen release claim

> Ordered payments admit proof-relevant, occurrence-indexed checking with
> exact computed residue. Under exact attempt-level catalog completeness,
> paid global plans and paid catalog plans are equivalent without replacing
> native receipts, expected-payment evidence, payment traces, or residue.
> Endpoint-only completeness is insufficient.

This is a repository-integration theorem family, not a new proof calculus or a
complexity result.

The extraction campaign closed in three bounded stages: V11-A froze the
generic `Payment` and `Catalog` API after duplicate-removal review; V11-B
passed with an independent premise-ablation countermodel, a public-only corpus
application, and SCRATCH-dependent annex forcing evidence; V11-C directly
promoted the two new paid modules and recorded the evidence without importing
it. As the post-release addendum records, that direct root already inherited
the five-module checker/WDC foundation whose legacy custody labels were later
corrected; “two-module” described the new paid layer, not the complete stable
import closure.

## Stable public theorem family

The stable root is `LeanProofs.Witnessed.PaidRecomposition`. Its complete
direct import list is:

```lean
import LeanProofs.Witnessed.PaidRecomposition.Payment
import LeanProofs.Witnessed.PaidRecomposition.Catalog
```

It imports no application, countermodel, SCRATCH module, Mathlib module, PC-1,
or PC-2 material.

### Payment

`Payment.lean` reuses `ResourceChecker.removeAt` as the authoritative payment
certificate. The public family is:

- `PaymentTrace`: an ordered sequence of exact removal equations, with every
  `occurrenceIndex` a position in the current wallet;
- `PaymentRefusal` and `PaymentRefusal.sound`: candidate-relative negative
  evidence for the same expected map, submitted order, and wallet;
- `checkPayment`: a total positive-or-negative checker;
- `checkPayment_accepts_iff`: checker acceptance exactly when a trace exists;
- `PaymentTrace.length_conservation`: exact resource-count conservation from
  the computed residue.

There is no duplicate membership receipt, `List.erase` certificate, persistent
serial, transition, or plan generator.

### Catalog

`Catalog.lean` retains exact attempt identity and dependent native positive
receipts:

- `PaidGlobalEdge` and `PaidCatalogEdge`;
- `ExactPaidCatalogComplete`;
- `PaidGlobalPlan` and `PaidCatalogPlan`;
- exact edge/plan conversions and round-trip receipts;
- `exact_catalog_adequate`;
- `exact_complete_globalizes_refusal`.

Catalog-to-global conversion is unconditional and forgets only exact catalog
membership. Global-to-catalog conversion requires
`ExactPaidCatalogComplete`, a premise over individual admitted attempts and
their native positive receipts—not a plan, search result, or desired refusal.

`PaidGlobalPlan.injectiveOn` is inherited plan plumbing. The singleton corpus
application supplies no nontrivial injectivity or matching evidence, and v11
makes none.

## Three claim scopes

The public types and release prose keep these propositions separate:

1. **One submitted attempt is accepted.** A consumer supplies its native
   `Positive attempt` receipt, such as an exact resident checker equation.
2. **No accepted plan exists in one named catalog.** This is
   `¬ Nonempty (PaidCatalogPlan ... catalog ...)`; it says nothing about
   attempts absent from that catalog.
3. **No global realization exists under exact completeness.** Only
   `exact_complete_globalizes_refusal`, with an explicit
   `ExactPaidCatalogComplete` premise, moves from catalog-relative to global
   nonexistence.

`ResourceCheckerExec.checkTrace = none` belongs only to the first, submitted-
trace scope. It does not provide an offender, a catalog refusal, or a global
refusal.

## Evidence custody

| Evidence | Custody | Release role |
| --- | --- | --- |
| `Applications/ResourceTraceOneCrossing.lean` | ANNEX: public evidence, Mathlib-free and non-SCRATCH | End-to-end resident application. Uses `ResourceCheckerExec.Trace Nat` as the attempt and the exact native acceptance equation as the dependent receipt; reconstructs resident `Checks`/`Derives`; preserves receipt, expected map, payment trace, and residue through catalog/global conversion. |
| `Countermodels/EndpointCompleteness.lean` | ANNEX: public countermodel, Mathlib-free and non-SCRATCH | Premise ablation. Authorized and forged attempts share endpoints but differ in exact identity, dependent positive content, and expected payment. A forged-only endpoint-complete catalog cannot realize the authorized plan and is not exact-complete. |
| `Applications/FiniteSupportOneCrossing.lean` | ANNEX with explicit SCRATCH dependency | Retains the native finite-support acceptance equation, normalized derivation, positional provenance, native resource-checker acceptance, exact occurrence removal/residue, and accepted-path obligation residue. Its deficient submission recovers the resident typed offender and excess-demand theorem. |

The fixed three-cycle fixture was intentionally not promoted. It adds no
independent evidence beyond the generic payment family, premise-ablation
countermodel, public-only corpus application, and finite-support forcing case.

None of these evidence modules is imported by the stable root.

## Exact nonclaims

- no new cut connective or proof calculus;
- no Hall, matching, 3DM, CSP, or complexity novelty;
- no general plan synthesis;
- occurrence indices are context-relative positions, not persistent serials;
- `ResourceCheckerExec.checkTrace = none` means only rejection of that
  submitted trace;
- no refusal transition or refusal debt-preservation;
- no dynamic authority, resource creation, or temporal debt;
- no nontrivial injectivity or matching evidence from the singleton corpus
  application;
- PC-1 and PC-2 remain closed;
- stateful bounded realization/refusal remains the next frontier.

Catalog refusal is a proposition scoped to its named catalog. V11 has no
transition semantics, and the absence of a modeled transition is not elevated
into a non-transition theorem.

## Promotion and audit gates

The release is ready only if all of the following are true in the final
post-wiring tree:

1. the stable root imports exactly `Payment` and `Catalog`, and
   `LeanProofs.Witnessed` imports that root;
2. stable import closure is transitively Mathlib-free and SCRATCH-free, and
   excludes all applications/countermodels;
3. custody enforcement classifies the directly promoted paid layer and the
   evidence exactly as recorded at v11 readiness time; the post-release
   addendum records the later correction of its inherited foundation;
4. `check-paid-recomposition-footprint.sh` enforces source custody markers,
   frozen import closure, placeholder/sorry absence, theorem/API footprint,
   expected axiom classes, Mathlib freedom, and evidence exclusion;
5. the claim register, paper map, frontier register, README, changelog, and
   citation metadata state the same claim scopes and nonclaims;
6. the complete repository verification envelope below exits zero.

## Post-wiring verification receipt

The commands below were run directly from the repository root. The recorded
values are their bare exit codes; no piped-output status was substituted for a
command status.

| Command | Exit |
| --- | ---: |
| `lake build` | 0 |
| `lake build Witnessed` | 0 |
| `lake build LeanProofs.Witnessed.PaidRecomposition` | 0 |
| `lake build LeanProofs.Witnessed.PaidRecomposition.Payment LeanProofs.Witnessed.PaidRecomposition.Catalog` | 0 |
| `lake build LeanProofs.Witnessed.PaidRecomposition.Applications.ResourceTraceOneCrossing` | 0 |
| `lake build LeanProofs.Witnessed.PaidRecomposition.Countermodels.EndpointCompleteness` | 0 |
| `lake build LeanProofs.Witnessed.PaidRecomposition.Applications.FiniteSupportOneCrossing` | 0 |
| `lake build PaidRecompositionEvidence` | 0 |
| `lake build LeanProofs AdmissibilityMathlibIslands` | 0 |
| `lake build ViewSemantics ViewSemanticsApplications ViewSemanticsMathlibIslands` | 0 |
| `bash scripts/check-paid-recomposition-footprint.sh` | 0 |
| `bash scripts/check-witnessed-footprint.sh` | 0 |
| `bash scripts/check-viewsemantics-footprint.sh` | 0 |
| `bash scripts/check-viewsemantics-isolation.sh` | 0 |
| `bash scripts/audit-axioms.sh` | 0 |
| `bash scripts/audit-native-decide.sh` | 0 |
| `bash scripts/check-mathlib-pin.sh` | 0 |
| `bash scripts/check-custody-classes.sh` | 0 |
| `bash scripts/check-mathlib-free-targets.sh` | 0 |
| `git diff --check` | 0 |
| temporary-index `git diff --check`, including all eight new paths | 0 |
| repository Lean proof-hole scan | 0 |
| PaidRecomposition hole/placeholder scan | 0 |
| stable-root transitive import audit (paid footprint gate) | 0 |
| `CITATION.cff` YAML/version/date/title check | 0 |

The stable-root closure attested by the paid-recomposition gate is exactly:

```text
LeanProofs.Witnessed.PaidRecomposition
LeanProofs.Witnessed.PaidRecomposition.Payment
LeanProofs.Witnessed.PaidRecomposition.Catalog
LeanProofs.Witnessed.ResourceChecker
LeanProofs.Witnessed.ResourceSequent
LeanProofs.Witnessed.Sequent
LeanProofs.Witnessed.Derivation
LeanProofs.Witnessed.NoFreeLift
```

The `Witnessed` target owns those stable modules explicitly. It does not own
the application or countermodel modules; those remain in the separate,
non-default `PaidRecompositionEvidence` target.

## Operator boundary at readiness time

After every gate above is green and the release-prep commit is selected, the
remaining actions are operator-only:

1. commit the reviewed v11 tree;
2. create the annotated `v11.0.0` tag on that exact commit;
3. push the commit and tag as intended;
4. create the GitHub release from the prepared v11 changelog/ledger text;
5. verify the resulting Zenodo deposit/version DOI and update any external
   record only through the operator's release workflow.

This ledger performs none of those actions and authorizes no work on the
stateful frontier.
