# PJ Tranche D-prime Collapse Audit

Date: 2026-07-22

## Disposition

The audit does not refute PJ-A's faithful comparison mappings or B-prime's
exact native receipt-gap theorems. It does refute a stronger reading in which
PJ itself qualifies bridges, makes receipts unforgeable, forces receipt use,
or supplies a substantive generic anti-minting institution.

The generic B-prime result is **valid but extremely thin**. Its force comes
from an adapter-local empty receipt fiber, not from an independent generic law
of qualification.

## Constructive attacks

| Attack | Exact witness | Result |
|---|---|---|
| Fixed inhabited source/target pair | `fixed_mint_iff_exact_entitlement_inhabited` | A fixed-pair receipt-free minter is constructively equivalent to inhabitation of the exact `EntitledFrom` type. |
| Freely selectable receipts | `receiptsEverywhereGiveMint` | A receipt selector for every index pair constructs the total B-prime minter; target truth is accepted but is not load-bearing. |
| Proof-relevant receipt identity alone | `force_bearing_receipts_still_admit_total_mint` | Even the Bool-receipt fixture has a total minter when every receipt fiber is inhabited. |
| Context erasure | `erased_context_mints_previously_refused_crossing` | A raw PJ bridge preserving subject but not context admits the exact crossing refused by the native exact-index bridge. |
| Subject erasure | `erased_subject_mints_previously_refused_crossing` | The dual raw bridge admits the wrong-subject crossing. |
| Consumer ignores receipt identity | `admissible_consumer_need_not_use_receipt_identity` | The bounded consumer interface permits one constant observation for two distinct force-bearing receipts. |
| Unqualified raw bridge enters consumer | `unqualified_raw_bridge_enters_consumer` | `AdmissibleConsumer` does not independently verify campaign-level adapter qualification. |

All attacks use inhabited values; none relies on an empty target judgment.

## Field-collapse ledger

- Collapsing a dependent native receipt family to uniformly inhabited `Unit`
  removes the receipt gap on which B-prime relies.
- Erasing either context or subject from the receipt law changes which
  crossings are entitled while remaining a valid raw `IndexedJudgmentBridge`.
- Retaining Bool receipt identity does not help when a receipt can be chosen
  for every fiber.
- `AdmissibleConsumer` constrains its input type but does not require its
  implementation to discriminate receipt identities.
- The target may be independently true throughout. Accidental truth neither
  creates nor repairs source-relative entitlement.

The surviving statement is exact: an independently demonstrated empty native
receipt fiber defeats a total or pair-specific minter for that exact adapter.
PJ does not explain why the native fiber is empty; the source calculus and its
fidelity proof do.

## Rejected stronger readings

D-prime rejects the claims that B-prime establishes cryptographic
unforgeability, constructor secrecy, semantic bridge qualification,
institutional enforcement, functional receipt use, one-use spend, or a common
law of ownership. Those remain unproved or calculus-local.
