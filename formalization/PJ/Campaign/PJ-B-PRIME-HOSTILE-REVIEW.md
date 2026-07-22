# PJ Tranche B-prime Hostile Review

Date: 2026-07-22

## Defect found and removed

The first explored B-prime design added generic qualification metadata around
a bridge. Independent review found that its free qualification witness did
not derive lawfulness from the native calculus and risked storing the desired
conclusion. That design was discarded before serialization.

The candidate instead quantifies directly over frozen PJ-A bridges. Semantic
qualification remains in the separately ratified adapter fidelity packets;
the generic theorem receives only native indices, judgments, receipts, and
entitlements.

## Required hostile ledger

| Attack | Constructive witness | Result |
|---|---|---|
| Source and target both inhabited without exact receipt | exact-index wrong-context fixture; all three primary instance gaps | consumption remains unentitled |
| Receipt for wrong subject | `wrong_subject_remains_not_entitled` | full subject index remains load-bearing |
| Receipt for wrong context | `wrong_context_remains_not_entitled` | full context index remains load-bearing |
| Raw bridge-shaped data treated as self-qualifying | `collapsedBridge` is structurally valid but has no adapter qualification; its `Unit` receipt admits minting | raw inhabitation proves no semantic lawfulness |
| Consumer before/after exact receipt | `exact_receipt_is_sufficient_for_bounded_consumer` and the three positive instance consumers | the positive consumers derive their observations from native `targetEvidence` |
| Same apparent target, different bridge identity | `exactIndexBridge` versus `contextFlipBridge` | distinct native receipt families have distinct force and are not interchangeable |
| Receipt identity erased | Bool-force entitlements projected to `Unit` | no constructive left inverse exists |
| Accidental target truth repairs a gap | wrong-index, GT, Execution, and Someone packets | independent target truth does not supply source-relative entitlement |

At least one target is inhabited in every central and primary anti-minting
packet. No result relies on an empty target type. StaticRole separately tests
a distinct lawful-wiring boundary rather than overstating a same-bridge
inhabited-target specialization.

## Collapse and triviality findings

- Replacing dependent receipts with `Unit` constructs
  `ReceiptFreeMintAt`; exact receipt indexing is therefore load-bearing.
- Exact and context-flip bridges are genuine different transformations, not
  copied identity labels.
- The positive consumer calls native `targetEvidence`; it does not accept a
  separate target argument.
- Projection injectivity is conditional on a supplied constructive left
  inverse. It does not claim every presentation is lossless.
- `ReceiptFreeMintAt` is total over all index pairs. B-prime does not deny a
  closed receipt-free helper for a bridge whose every crossing is covered.
- The theorem rules out uniform or exact-gap minting, not all possible
  dishonest Lean definitions, runtime forgery, or institutional misuse.

## Frontier regression audit

No `Frontier`, `Remaining`, `RemainingAfter`, or `Obligations` identifier
occurs in executable B-prime Lean source. The rejected `PJ/TrancheB`
exploratory files remain absent. No common composition or residual theorem is
claimed under a synonym.

Independent hostile review disposition: **pass, narrowly and with the stated
limits**.
