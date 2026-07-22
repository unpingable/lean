# PJ-B Fast-Falsification Record

Date: 2026-07-22

## Verdict

`FRONTIER-NOT-COMPOSITIONAL`

PJ Tranche B stops at its chartered fast-falsification boundary.  PJ-5 found
a narrow exact-receipt anti-minting result, but PJ-6 did not find a
non-definitional common frontier law.  Therefore no PJ-B scientific candidate
is created, and Tranche C remains unopened.

## Ratified input

The work began from the exact PJ-A ratification chain:

- PJ-A scientific candidate:
  `d634517fc08205758de59466c97f5998f774dabb`;
- candidate tree:
  `c539b62398d30b5d12a40fdffef53eb543305705`;
- candidate parent:
  `99f3973aca420817ac4eb5a5a1282252326c32e7`;
- PJ-A operator ratification:
  `d1fad6efc608b7daf3b8a8f47b7f4cfc5a1c249e`;
- ratification tree:
  `706da052cb2dcff572054f686884f92bb43829ad`;
- frozen `PJ/Core.lean` SHA-256:
  `1d86bee97f92f2644d8605a05d6a31deaa3584f55582d4a09b638718ffff185c`.

The ratified PJ-A core was not changed during Tranche B.

## PJ-5 result: narrow support

The tested PJ-5 design separated independently available source evidence,
independently available target evidence, direct target consumption, and exact
source-relative receipt entitlement.  `TargetDemand.consumeEntitled` derived
target evidence through the frozen PJ-A entitlement object before consuming
it.  A receipt-gap fixture stored source evidence, target evidence, and a
constructive refusal of the exact receipt; it did not store an illegality bit
or the anti-entitlement conclusion.

The exact supported statement is:

> Accidental target truth and successful direct target use do not mint
> source-relative entitlement when the exact endpoint-bound receipt is
> constructively unavailable.

This specialized meaningfully to all three primary PJ-A instances:

- Governed Transport retained the image/nonimage route boundary, the missing
  positive-lift refusal, and the target-local-negative refusal;
- Execution Custody retained the complete stage index, separated attempt-only
  evidence from a different commit-ready stage, and preserved the local
  precondition refusal;
- Someone Continuity retained the exact `AgentId` boundary and native
  `OwnsPacket` reachability refusal.

This does **not** earn a general operational-illegality theory.  The central
anti-entitlement proof eliminates an alleged entitlement using exact receipt
refusal.  Source truth, target truth, demand, and native carry are load-bearing
in the surrounding non-implication packet, not in that elimination alone.

The two exploratory PJ-5 sources were deliberately not serialized as a
PJ-B candidate:

| Exploratory source | Lines | SHA-256 |
|---|---:|---|
| `PJ/TrancheB/IllegalLift.lean` | 188 | `47ae06e3a6d89293ce219a699730314e9f81e3370b48a2f7b502ffcba111b474` |
| `PJ/TrancheB/IllegalLiftInstances.lean` | 212 | `03f10460618b1e2328abf8d9d21bdb5893503aa121a112280486d48d9e596ccd` |

They compiled in a 20-job combined exploratory build, and all 22 explicitly
printed PJ-5 declarations were axiom-free.  Compilation establishes internal
consistency of the experiment; it does not overcome the failed PJ-B success
gate.

## PJ-6 hostile finding

The tested composition/frontier proposal was 341 lines with SHA-256
`5637c40484711e2d6bdd87a8743007bf71453b0ba17fdfc1afd029315c3fa634`.
It compiled, and all 15 explicitly printed declarations were axiom-free.  The
independent hostile review nevertheless found the claimed frontier result to
be projection-only:

1. `TwoLegChain` reconstructed two raw bridge-shaped records instead of
   retaining the identities of two already-qualified PJ-A bridge values.
2. `composite_target_is_two_native_carries` was `rfl`, so its content was
   ordinary function composition under newly introduced packaging.
3. `RemainingAfterFirst` and `RemainingAfterSecond` were aliases for the other
   receipt family, not independently forced frontier judgments.
4. `clearFirst_retains_second` and `clearSecond_retains_first` were `rfl`
   record-projection laws.
5. `clearFirst` treated possession of the first receipt as clearance without
   retaining source evidence or an actual first-leg entitlement.
6. `clearSecond` analogously omitted intermediate evidence and an actual
   second-leg entitlement.
7. A composite receipt existentially selected one middle index.  Failure at
   one selected middle therefore did not characterize the complete frontier
   when another middle could remain available.
8. Governed Transport has substantive native coverage obligations, while
   Execution Custody and Someone Continuity do not expose a common native
   frontier semantics.  Reusing the word “receipt” did not supply one.

These are exactly the theorem-by-definition and record-repacking attacks that
PJ-6 was required to survive.  A conditional two-step evidence helper could
be described as pure evidence sequencing, but it would not establish native
route composition, stateful realization, one-use behavior, or frontier
preservation.

## Exact missing structure

A future common frontier theorem would require a typed, source-forced
demand/resolution structure which:

- specializes nontrivially in all three primary calculi;
- distinguishes actual entitlement from receipt possession;
- retains unresolved obligations not addressed by a successful step;
- does not reduce resolution to constructor projection; and
- preserves each source calculus's native refusal and indeterminacy
  distinctions.

PJ-A contains no such structure, and the present three primary sources do not
force one.  No generic extension is earned from this experiment.

## Verification and disposition

The combined exploratory command

```text
lake build PJ.TrancheB.IllegalLift PJ.TrancheB.IllegalLiftInstances PJ.TrancheB.CompositionFrontier
```

completed successfully in 20 jobs.  All 37 explicitly printed exploratory
declarations were axiom-free.  `git diff --check` passed.  These checks show
that the rejected proposal was technically coherent; the rejection is
scientific, not a compile or axiom failure.

The three exploratory Lean files were removed after review and are not part
of this record commit.  No PJ core, source calculus, adapter, aggregate,
release surface, or sibling repository was changed.  No PJ-B candidate,
Tranche-C object, push, tag, mint, publication, release, runtime integration,
JCP implementation, or public theory naming was produced.
