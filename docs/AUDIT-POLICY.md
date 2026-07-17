# Audit Policy — what the gates check (and what "clean" means here)

> **The repository is not axiom-free; it is axiom-classified. WDC promoted receipts remain
> footprint-attested.**

> **v13 custody note.** The target contract classifies every retained public
> Lean source as an exact-root `STABLE-SURFACE`, terminal `PUBLIC-EVIDENCE`, or
> the root `REPOSITORY-AGGREGATE`. Incubation belongs in skunkworks. All 53
> live returns now have sibling homes, and the public whole-tree gate passes
> exactly over the 179 retained modules. The custody gate is independent of
> the axiom and footprint gates described here; a green result from one never
> substitutes for another. Migration
> status: [`V13-MIGRATION-LEDGER.md`](V13-MIGRATION-LEDGER.md).

That is the honest fence. An `axiom` in Lean is a hole the kernel agrees not to inspect — a
trust import. The job of these gates is not to ban axioms (this repo legitimately uses
abstract carriers, uninterpreted stores, abstract time, and fenced scenario specimens). The
job is to make the **trust bill impossible to hide**: every hole is classified, and the
forbidden class — claim-bodied placeholders — is held at zero.

The independent gates are run from `scripts/`. The sections below explain the
receipt-specific gates and the repository-wide classifiers.

## 1. WDC receipt footprint — `check-witnessed-footprint.sh`

Builds the Mathlib-free `Witnessed` library and re-attests each ratified receipt's exact
axiom footprint (`#print axioms`) against `RATIFICATION-v1.3.md`. Fail-closed (`set -euo
pipefail`, the `lake env lean` probe is explicitly guarded). Receipt footprints are exactly
one of: **none** / **propext** / **propext + Quot.sound**. The WDC surface is the cleanest
in the repo and is **not** diluted with repo-wide exceptions.

12 receipts as of the WDC 2.0 surface (incl. `AbstractNormalization.normal_form_iff_of_commutes`
and `CommutesNecessity.commutes_is_necessary`, both axiom-free).

## 2. Repo axiom classifier — `audit-axioms.sh` + `axiom-policy.tsv`

Every declared `axiom`/`constant` under `LeanProofs/` must be classified. Fail-closed on
**unclassified** or **forbidden** declarations. Classes:

| Class | Meaning | Verdict |
|---|---|---|
| **signature** | uninterpreted carrier / op / predicate *symbol* — declares vocabulary, asserts no claim (`axiom Time : Type`, `axiom Time.le : Time → Time → Prop`) | allowed |
| **interface-law** | a Prop-valued *law* constraining an abstract interface (`axiom le_trans : …`) | allowed only when marked + footprint-visible; dependent theorems are **not** "axiom-free" but "relative to the interface law" (currently 0 in repo) |
| **specimen** | concrete scenario stipulation for a fenced counterexample (`defendedValue_initial : … = 1`) | allowed only inside a labeled specimen module; must not silently support a broad structural receipt |
| **forbidden** | claim-bodied placeholder (the fake-mustache class: a theorem-shaped axiom standing in for a desired doctrine — e.g. the removed `persistence_normalizes : ∀ d, d≠.dh → True`) | **zero tolerance** |

Current v13-migration checkpoint census: 23 signature, 0 interface-law, 8
specimen, **0 forbidden**, and 0 unclassified. The authoritative receipt is
always the bare exit and report of `scripts/audit-axioms.sh`, not this prose
count.
The distinction that matters mechanically: *is the axiom a proof of a proposition, or an
uninterpreted symbol used to state a generic theory?* `Time.le` returns `Prop` but is a
predicate symbol (signature); `∀ x, Time.le x x` would be a law (interface-law).

## 2a. PaidRecomposition stable footprint — `check-paid-recomposition-footprint.sh`

Re-attests the v11 `LeanProofs.Witnessed.PaidRecomposition` surface after the
v13 custody correction. The gate fixes the exact eight-module stable closure as
`PUBLIC-SHIPPED`: the paid root, `Payment`, `Catalog`, `ResourceChecker`,
`ResourceSequent`, `Sequent`, `Derivation`, and `NoFreeLift`. It fixes the three
evidence modules as `PUBLIC-EVIDENCE`, requires the two-import paid root, checks
`Witnessed` build ownership excluding evidence, and rejects Mathlib, evidence,
application, or countermodel modules in the stable transitive closure. The foundation's
reclassification changes no definition or theorem; it records the closure on
which the v11 stable API already depended.

The same gate freezes the paid API plus the entire named foundation surface:
15 types/definitions, all 18 constructors, both scoped notations, and all 45
public foundation theorems. The promoted theorem footprints are exactly 30
axiom-free and 15 using `propext`; the seven pre-existing paid receipts retain
their separately fixed footprints. It scans the entire stable/evidence
registry for holes and builds the separate evidence target.
`Applications.FiniteSupportOneCrossing` now imports the corrected public
`LeanProofs.CustodyIndexed.FiniteSupportChecker` foundation.  The former
symbolic Scratch exception is gone; no public module may import a residual
`LeanProofs.Scratch.*` namespace.

## 2b. Judgment Orientation footprint — `check-judgment-orientation-footprint.sh`

Builds the stable `JudgmentOrientation` family and its separately imported
`JudgmentOrientationEvidence` public evidence, then re-attests thirteen frozen
receipts
across `Core`, `Attribution`, `Provenance`, `OriginSupport`, and `Bridge`.
Every receipt must match its exact expected footprint. The disclosed family
maximum is `[propext, Classical.choice, Quot.sound]`; the core confinement
laws are constructive. Missing or renamed receipts, `sorryAx`, added axioms,
or footprint drift fail closed.

## 3. native_decide policy — `audit-native-decide.sh` + `native-decide-policy.tsv`

`native_decide` is allowed only in finite-computational-witness modules
(`PersistenceModel`, `BranchSelector` — Δt finite traces). Forbidden in WDC metatheory,
admissibility kernels, and structural public receipts. Not a purity cult; a classifier.

## 4. mathlib pin drift — `check-mathlib-pin.sh`

`lakefile.toml`'s mathlib `rev` must equal the resolved commit in `lake-manifest.json` (a
full 40-char SHA, never a moving ref like `master`). Moving mathlib is explicit: `lake
update` → inspect → repin → rerun gates. Never silent.

## 5. ViewSemantics stable/evidence footprint — `check-viewsemantics-footprint.sh`

Builds the stable, public-evidence, and explicit Mathlib-evidence targets and
re-attests the exact footprints of the
shared semantics, bounded-projection theorems, proof-carrying checker,
composition specimens, reuse adapters, resident bridge-ontology adjudication,
authorized-trace adapter, non-XOR application, and P25 island. Structural and
checker receipts must be axiom-free; the BindingSource quotient adapter is
exactly `[propext, Quot.sound]`; the P25 bridge is exactly
`[propext, Classical.choice, Quot.sound]`; and trace separation receipts must
match the v9 authorization walls they reuse.

## 6. ViewSemantics import/custody isolation — `check-viewsemantics-isolation.sh`

Walks the static import closures of the stable and Mathlib-free evidence
targets. Both must remain Mathlib-free, P25 must remain in its explicit
evidence island, and the stable root may not absorb application/evidence
modules. There is no raw-Scratch allowlist.

## 7. Whole-tree custody — `check-custody-classes.sh`

Enumerates every existing tracked or untracked Lean source in the repository,
not merely one directory or a hand-selected subset.  It requires exactly one
recognized `Custody-Class` and `Surface-Role`, exact registry coverage, no
residual Scratch path/import, and closure agreement for every registered
stable root.  It fails closed on new unregistered files. Evidence-target
ownership is checked separately; this gate does not infer Lake target
membership from a custody role.

This corrects the pre-v13 checker, which examined 84 of 244 modules under
`LeanProofs/` while the full v12 source tree contained 271 Lean files.  The old
green receipt remains historical evidence about its partial registry only.
At the current checkpoint, the actual public tree passes exactly at 179 files
(82 stable, 96 evidence, one aggregate), ten roots, and 98 ownership
relations. The strengthened public-target gate separately passes its exact
target closures and declared Mathlib-free and ownership manifests at this
checkpoint. Its exact receipt is described separately below.

## 8. Exact public targets and Mathlib closure — `check-mathlib-free-targets.sh`

Validates every repository-owned Lake project and `lean_lib` against the
project-keyed five-column `scripts/public-targets.tsv` registry: project,
target, target role, import policy, and build policy. It computes each exact
local target closure, checks target/module ownership, and rejects Mathlib
reachability from current-tree targets declared Mathlib-free. It also checks
the reverse direction: every custody-registered public source must have at
least one role-compatible registered target owner (stable through a stable
target, evidence through an evidence target or the exact repository aggregate,
and the aggregate through its aggregate target).

For a `pinned-external` target, the gate does not mislabel an external release
closure as current-tree or Mathlib-free. It instead requires explicit Git
requirements, an exact resolved commit in the committed Lake manifest, and
agreement between the lakefile request and manifest lock before allowing the
declared external import boundary. This is the evidence/stable target receipt
that the whole-tree custody gate deliberately does not provide.

Current exact receipt: two repository-owned Lake projects, 23 public targets,
23 exact local closures, 19 Mathlib-free current-tree targets, 463 local
target/module ownerships, one pinned-external target, and one locked external
boundary, with role-compatible target ownership for 179/179 public sources.
Mathlib-reaching targets remain explicit-only. The nested downstream consumer's
bare build completes 19 jobs in CI.

## What "clean" means, by surface

- **WDC promoted receipts** — axiom-free or tiny known footprints (propext / Quot.sound), build-graph-enforced Mathlib-free.
- **Abstract kernel interfaces** — allowed, labeled (signature class).
- **Interface laws** — allowed, footprint-visible; results are relative-to-the-law, not absolute.
- **Scenario specimens** — public evidence or skunkworks incubation according
  to maturity; never silently absorbed by a stable root.
- **Claim-bodied placeholders** — forbidden, held at zero.
- **Computational finite witnesses** — `native_decide`, confined to allowed modules.

## Running the full battery

```
lake build
lake build Witnessed
lake build WitnessedEvidence
lake build PaidRecompositionEvidence
lake build JudgmentOrientation JudgmentOrientationEvidence
lake build CustodyIndexed CustodyIndexedEvidence
lake build PathVerdict PathVerdictEvidence
lake build LeanProofs AdmissibilityEvidenceMathlib
lake build ViewSemantics ViewSemanticsEvidence ViewSemanticsEvidenceMathlib
(cd downstream/wdc-v2-consumer && lake build)
scripts/check-witnessed-footprint.sh
scripts/check-paid-recomposition-footprint.sh
scripts/check-judgment-orientation-footprint.sh
scripts/check-viewsemantics-footprint.sh
scripts/check-viewsemantics-isolation.sh
scripts/audit-axioms.sh
scripts/audit-native-decide.sh
scripts/check-custody-classes.sh
scripts/check-mathlib-pin.sh
scripts/check-mathlib-free-targets.sh
```
