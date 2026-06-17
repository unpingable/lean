# Composition Classification — INVALIDATED TARGET / findings record

**Status: prior target invalidated (2026-06-16).** The earlier target —
`classify : Attempt Bridge → Bool → Outcome`, a single classifier over
`(attempt × validity)` — assumed same-axis bridge paths and cross-axis conversion
attempts share one domain. Source inspection + an adversarial pass (codex, gpt-5.5)
refuted it. This file is now a **findings record, not a design.** Replacing the dead
single-classifier with a confident "two-register classifier" would just be the next
attractive mistake in a cleaner jacket — the honest status is narrower.

**Status update: gate retired, not merely undefined (2026-06-17).** A further pass
(adversarial review by a non-Claude, source-grounded reviewer over the quarry copy in
`~/git/playground/wired`, plus a compiled reach-floor demotion there) prosecuted the
*general* composition-classification gate, not just the single-classifier form. Outcome:

> The proposed composition-classification gate was investigated and found unsuitable.
> Semantic bridge validity does not support the intended exclusive classification
> (`naive_exclusivity_fails`: a `BridgeValid` cross-edge can preserve `Sem` yet still add
> derivational reach over a floor), and the replacement reach-floor condition reduces to
> ordinary ancestor coverage (`reachFloor_iff_ancestor_covered`, compiled in the quarry).
> No successor promotion criterion has yet been adopted.

This is a **retirement of the target**, not a parked open theorem. The species classifier
`classifyStep` is *total as a function*; what is partial — and not strengthenable in this
model without a new assumption — is the soundness/exclusivity story. The word *calculus* is
withheld. The sections below are preserved as the prior open-gate framing, now historical:
do not read "what a real theorem must define" as "build it."

## Why the prior target is dead

Real `Embedding.Bridge` is same-axis BY CONSTRUCTION (`bridge_both_freshness`; cross
edges definitionally `False`). So:
- cross-axis conversion is NOT an `Attempt Bridge` — it can't be a value the
  classifier ranges over;
- same-axis and cross-axis are different domains, not two branches of one.

## Current proved artifact (the whole of it)

- `Wired.CompositionClassification.freshness_two_step_lift_sound` — length-2 paid
  `Lift` soundness for freshness (`Sem` holds at the end of a 2-step same-axis path).
  - It is **path soundness**, NOT bridge-relation closure and NOT a classification
    theorem. It is `paid_lift_sound` at length 2 — near-trivial — and it accepts
    degenerate/weakening steps.

That is the only theorem. Everything below is unbuilt.

## Recorded corrections (do not re-lose these)

1. `freshness_two_step_lift_sound` is path soundness, not composition closure.
2. The freshness `Bridge` RELATION is not closed into a direct bridge (two
   carry-forwards = carry THEN weaken, by triangle's `≥`). The PATH is closed/sound.
3. Cross-axis cases are not `Attempt Bridge` cases.
4. "Two registers" is a useful explanatory split, NOT yet a partition theorem.
5. `redundant` is contaminated: `Embedding.valid_cross_bridge_is_redundant` proves
   only semantic TRUTH of the target under `BridgeValid`, not "adds no reach." It is
   a reachability claim in disguise. **Owner: AG-Claude / `Embedding.lean`.**

## Open gate — what a real composition-classification theorem must first define

1. The **domain** of attempted moves: real bridge paths (1-step, n-step), purported
   cross-axis conversions, malformed attempts, and same/cross species cases —
   explicitly and exhaustively.
2. Outcome **semantics** for `composable` / `refused` / `redundant` (semantics, not
   enum labels nothing references).
3. **Soundness** of each outcome.
4. Whether coverage is **exhaustive and exclusive.**

## Naming fences (earned, not declared)

- Do NOT use `Trichotomy` until exhaustiveness AND exclusivity are proved.
- Do NOT use `redundant` until the cross-edge theorem proves non-reach /
  non-contribution — or rename the outcome to match the weaker theorem. Candidate
  honest names for the current theorem shape:
  - `valid_cross_bridge_target_true`
  - `valid_cross_bridge_preserves_truth`
  - `valid_cross_bridge_semantically_vacuous` (only if it really proves vacuity)
- `composition_classification`, NOT `composition_trichotomy` (earlier fence, still in force).

## Next Lean work (NOT a classifier)

Either: strengthen/rename the cross-edge "redundant" theorem (owner AG-Claude); or
generalize `freshness_two_step_lift_sound` to n-step path soundness IF that is
meaningful and not already trivial from `Lift`. **Do not build another classifier yet.**
