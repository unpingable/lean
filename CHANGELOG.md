# Changelog

Release history for **Admissibility Kernels** (Lean stack). Versions correspond
to Zenodo deposits under the concept DOI
[10.5281/zenodo.20369489](https://doi.org/10.5281/zenodo.20369489); the GitHub
release tag drives the deposit. Versions prior to 1.2.0 are recorded on Zenodo.

## Unreleased — composition gate prosecuted and retired (2026-06-17)

A **status correction**, not new public mathematics. The `composition_classification`
promotion gate named in v1.2.0 was attempted and adversarially reviewed (non-Claude,
source-grounded, over the quarry copy); the result is a *retirement* of that target, not
progress toward it.

### Findings (no public-surface change)
- Attempted and adversarially reviewed the proposed composition gate; semantic bridge
  validity does not support the intended exclusive classification (`naive_exclusivity_fails`).
- Retained as durable corrections: arbitrary-length paid-path transport (framed as
  transport, not a calculus) and the semantic-truth ⊬ derivational-reach separation.
- Corrected the bridge non-closure account (carry-then-weaken; the *path* is sound, the
  one-step *relation* is not closed).
- Demoted the reach-floor closure condition to ordinary graph reachability / ancestor
  coverage.
- Withheld the word *calculus*; no successor promotion criterion adopted.

### Does not change
- The **1.0 public theorem surface** and all its non-claims — *unchanged*.
- "Calculus of attestation boundaries" was already a *destination* claim, not a present
  one. It remains a destination only; the specific gate proposed to earn it is now retired
  rather than pending. Findings record: `experiments/no_free_lift_wiring/COMPOSITION-CLASSIFICATION-TARGET.md`.

## v1.2.0 — No Free Lift candidate annexes (2026-06-16)

A **semantic / governance release**, not new public mathematics. It adds fenced
candidate and experimental material — shipped with its naming boundaries already
corrected — and records a version boundary: the No-Free-Lift work establishes a
formal **theory of attestation boundaries**, **not yet a calculus**.

### Adds
- Fenced `UNRATIFIED-CANDIDATE` annexes in `LeanProofs/Admissibility/`:
  `NoFreeLift.lean` (the paid-bridge-closure spine) and `CarryLaws.lean` (the two
  coordinate cost laws). Axiom-free, **unwired** (not imported by `LeanProofs.lean`),
  committed `94df70e`.
- A fenced **`experiments/` tree** (`Custody-Class: EXPERIMENTAL-WIRING`, its own
  Lake project, not imported by the canonical surface) containing
  `no_free_lift_wiring/` — the spine wired to modeled freshness/authority
  embeddings — with its audit (`WIRING-AUDIT.md`) and a ratification template
  (`RATIFICATION-PENDING.md`) coupled to the code.
- `COMPOSITION-CLASSIFICATION-TARGET.md` — names the theorem
  (`composition_classification`) required to promote the work toward any future
  "calculus of attestation boundaries" claim.

### Changes (experimental wiring de-placarded before release; no proof changed)
- `Wired.Contraction` → `Wired.BudgetMonotonicity` (proves the *metric* budget law,
  not the structural contraction rule).
- `Wired.Composition` → `Wired.CoCompilation` (proves co-compilation `True`, not a
  composition result).
- `composition_builds` → `modules_cocompile`.
- Removed a `"calculus is legal for this object"` overclaim from the aggregator
  docstring. Old names retained only as provenance notes.

### Does not change
- The **1.0 public theorem surface** (`AdmissibilityKernels`, the eight `[1.0]`
  modules) and all its non-claims — *unchanged*. This release adds material; it
  does not correct any public-surface "calculus" drift, because there was none.
- Ratification status: nothing promoted.
- No present-tense "calculus" claim; no substructural claim; no substantive
  composition theorem.

### Status
- `No Free Lift` is **canonical-tracked / candidate**, not canonical-ratified.
- "Calculus of attestation boundaries" remains a **destination** claim, gated on
  `composition_classification` (theory → calculus → substructural → conditional
  model→world; see the target doc). The word is not earned yet.
