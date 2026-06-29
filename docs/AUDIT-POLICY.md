# Audit Policy — what the gates check (and what "clean" means here)

> **The repository is not axiom-free; it is axiom-classified. WDC promoted receipts remain
> footprint-attested.**

That is the honest fence. An `axiom` in Lean is a hole the kernel agrees not to inspect — a
trust import. The job of these gates is not to ban axioms (this repo legitimately uses
abstract carriers, uninterpreted stores, abstract time, and fenced scenario specimens). The
job is to make the **trust bill impossible to hide**: every hole is classified, and the
forbidden class — claim-bodied placeholders — is held at zero.

Four independent gates, run from `scripts/`:

## 1. WDC receipt footprint — `check-witnessed-footprint.sh`

Builds the Mathlib-free `Witnessed` library and re-attests each ratified receipt's exact
axiom footprint (`#print axioms`) against `RATIFICATION-v1.3.md`. Fail-closed (`set -euo
pipefail`, the `lake env lean` probe is explicitly guarded). Receipt footprints are exactly
one of: **none** / **propext** / **propext + Quot.sound**. The WDC surface is the cleanest
in the repo and is **not** diluted with repo-wide exceptions.

12 receipts as of the WDC 2.0 candidate (incl. `AbstractNormalization.normal_form_iff_of_commutes`
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

Current census: 23 signature, 0 interface-law, 8 specimen, **0 forbidden**, 0 unclassified.
The distinction that matters mechanically: *is the axiom a proof of a proposition, or an
uninterpreted symbol used to state a generic theory?* `Time.le` returns `Prop` but is a
predicate symbol (signature); `∀ x, Time.le x x` would be a law (interface-law).

## 3. native_decide policy — `audit-native-decide.sh` + `native-decide-policy.tsv`

`native_decide` is allowed only in finite-computational-witness modules
(`PersistenceModel`, `BranchSelector` — Δt finite traces). Forbidden in WDC metatheory,
admissibility kernels, and structural public receipts. Not a purity cult; a classifier.

## 4. mathlib pin drift — `check-mathlib-pin.sh`

`lakefile.toml`'s mathlib `rev` must equal the resolved commit in `lake-manifest.json` (a
full 40-char SHA, never a moving ref like `master`). Moving mathlib is explicit: `lake
update` → inspect → repin → rerun gates. Never silent.

## What "clean" means, by surface

- **WDC promoted receipts** — axiom-free or tiny known footprints (propext / Quot.sound), build-graph-enforced Mathlib-free.
- **Abstract kernel interfaces** — allowed, labeled (signature class).
- **Interface laws** — allowed, footprint-visible; results are relative-to-the-law, not absolute.
- **Scenario specimens** — fenced (specimen class), not released into the theorem preserve.
- **Claim-bodied placeholders** — forbidden, held at zero.
- **Computational finite witnesses** — `native_decide`, confined to allowed modules.

## Running the full battery

```
lake build
scripts/check-witnessed-footprint.sh
scripts/audit-axioms.sh
scripts/audit-native-decide.sh
scripts/check-mathlib-pin.sh
```
