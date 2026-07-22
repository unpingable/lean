# PJ-1 — Minimal Indexed Judgment Signature

Date frozen for held-out testing: 2026-07-22

## Frozen candidate

The PJ-1 signature is `PJ.IndexedJudgmentBridge` in `PJ/Core.lean`.

Frozen source SHA-256:

```text
1d86bee97f92f2644d8605a05d6a31deaa3584f55582d4a09b638718ffff185c
```

The hash was recorded only after GT, Execution Custody, and Someone
Continuity compiled against the same file without requiring an extension.
The file must remain byte-exact during the held-out StaticRole test.

## Exact signature

One value represents one native oriented rule:

```lean
structure IndexedJudgmentBridge where
  SourceIndex : Type uSource
  TargetIndex : Type uTarget
  SourceJudgment : SourceIndex → Sort uSourceJudgment
  TargetJudgment : TargetIndex → Sort uTargetJudgment
  Receipt : SourceIndex → TargetIndex → Sort uReceipt
  carry : {source : SourceIndex} → {target : TargetIndex} →
    Receipt source target →
    SourceJudgment source →
    TargetJudgment target
```

`EntitledFrom bridge source target` is a derived evidence object containing
the exact source evidence and receipt. Its target evidence is obtained by
`carry`; the target conclusion is not stored in the entitlement.

`NotEntitledFrom` is the constructive absence of that exact pair. It is not
target falsity and therefore permits a target judgment to be independently or
accidentally true without being licensed from the named source.

## Why this is not `Thing` plus `Related`

The signature keeps five distinctions that a universal relation erases:

1. source and target indices may be different types;
2. source and target judgment families are independently indexed;
3. bare target evidence is distinct from source-relative entitlement;
4. the receipt is an evidence-bearing type indexed by both endpoints;
5. the only target-production operation consumes both the receipt and exact
   source evidence.

The adapters may not define a receipt that simply stores the target
conclusion. That nontriviality obligation is verified per instance rather
than represented by a Boolean or a proof field that restates the desired
theorem.

## Field-removal experiments

| Removed or collapsed field | Exact loss |
|---|---|
| `SourceIndex` | GT source-fiber binding, Execution source-stage binding, and Someone origin agent can be replayed across sources. |
| `TargetIndex` | GT image scope globalizes; Execution destination stage and Someone destination agent are erased. |
| heterogeneous source/target index types | GT is forced into a sum/product adapter solely to simulate its unchanged heterogeneous endpoints. |
| `SourceJudgment` | a receipt alone can mint a target; GT artifacts, Execution prior-stage evidence, and Someone preserved invariant all disappear. |
| `TargetJudgment` | target truth is collapsed into the bridge receipt, so accidental truth versus entitlement cannot be stated. |
| `Receipt` | `carry` becomes a total free lift; exact GT routes, Execution side conditions, and Someone reachability vanish. |
| evidence-bearing `Receipt` replaced by `Bool` | proof-relevant GT fibers and native rule premises become lossy flags. |
| `carry` | the object becomes vocabulary-only and proves no licensed local transition. |

Every retained primitive field is used substantively by all three primary
adapters. `EntitledFrom` and `NotEntitledFrom` are derived definitions, not
additional primitive authority.

## Rejected signature variants

### `Thing` and `Related`

Rejected as `COMMON-SIGNATURE-TRIVIAL`: it cannot distinguish source evidence,
target truth, or exact bridge evidence.

### Total source-to-target function

Rejected because it makes a bridge available for every source and erases GT
coverage, Execution side conditions, and Someone nonreachability.

### Receipt stores target evidence

Rejected because `EntitledFrom` would contain the conclusion that `carry` is
supposed to earn.

### One mega judgment/bridge enum

Rejected as convenience-only packaging. Each native rule is one bridge value;
local kinds do not enter the shared core.

### Generic refusal or outcome sum

Rejected. GT negative transport, Execution refusal/unknown, and Someone
proposition-level nonreachability do not share one exact eliminator.

### Generic composition, identity, owner, custody, spend, frontier, or context transport

Rejected from PJ-1. GT and Someone have different local composition laws;
Execution Custody deliberately has none. Institutional and conservation
structure remains later classification work.

## Adapter qualification rule

The small core cannot prevent a dishonest instance from choosing `Receipt :=
Unit` and ignoring its arguments. Adding a generic `nontrivial := true` field
would merely store the desired conclusion. Each adapter must instead show:

- its receipt is constructed from exact native premises;
- its `carry` is the native constructor or theorem;
- it does not store its target judgment inside the receipt;
- at least one native hostile or non-implication remains visible through
  `NotEntitledFrom`;
- omitted local laws remain explicit rather than silently weakened.

The three primary adapters satisfy this obligation. The held-out test may now
inspect StaticRole but may not change this signature.
