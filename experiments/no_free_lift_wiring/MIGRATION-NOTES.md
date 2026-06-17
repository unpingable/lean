# Migration Notes — playground quarry → canonical Successor (v1.3 candidate)

## Quarry divergence constraint (HARD — operational knowledge, not chat debris)

The witnessed-derivation work was developed in a playground quarry (`~/git/playground/wired/`) that
forked from a **pre-v1.2** state of this experiment tree. Its `Wired/` spine is therefore **not**
canonical's:

- canonical carries the v1.2 renames `Composition → CoCompilation` and
  `Contraction → BudgetMonotonicity`; the quarry still has the old names;
- `CompositionClassification.lean`, `ConsumerFreshness.lean`, `Families.lean` also differ.

**Rule: dependency-cone port only. Bulk-merging the quarry `Wired/` is FORBIDDEN** — it would revert
the v1.2 renames and clobber the public-facing spine.

The Successor calculus core ported safely **only because** its dependency cone — `Embedding`,
`NoFreeLift`, `Authority`, `Freshness`, `Divergence`, `Coordinates`, `CarryLaws` — is byte-identical
across both repos (verified by `diff` at port time). Any future port MUST re-verify cone identity
before copying a single file.

## What landed (`Successor/`, EXPERIMENTAL-WIRING, NOT in `defaultTargets`)

- `WitnessedDerivation.lean` — the defined judgment `Lift` + composition + non-manufacture.
- `Normalization.lean` — the canonical-form theorem (earns the name) for the freshness model.
- `Tightened.lean` — the four-axis model-admission discipline `WitnessedDiscipline`
  (`bridge_valid` / `semantic_nontrivial` / `bridge_selective` / `properly_live`).
- `DisciplineObstruction.lean` — `Discriminating` retired here + the factorization theorem
  `bridgeValid_discriminating_iff_semanticNontrivial`.

Ratification basis: `RATIFICATION-v1.3.md`. Build: `lake build Successor` (green; nothing exceeds
`[propext, Quot.sound]`; no `sorry`).

## Central fact to preserve

Normalization earned the calculus on the rule system **as it stood**; the four-axis discipline is a
model-admission filter **beside** the calculus (`Normalization` never imports it). The bridge-selectivity
axis repaired a weak model-filter axis (the retired `Discriminating`); it did **not** enlarge the
calculus, and it is not its retroactive admission ticket.

Public 1.2 surface untouched; this is the **v1.3 candidate** experiment surface, not a 2.0 release.
