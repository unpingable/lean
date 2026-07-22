# PJ Tranche D-prime Theorem Inventory

Date: 2026-07-22

## Executable additions

D-prime adds 38 compiled declarations in two isolated modules:

- `PJ.TrancheDPrime.CollapseHostiles`: 17 declarations;
- `PJ.TrancheDPrime.OutOfSampleAdmissibility`: 21 declarations.

All 38 are axiom-free. The direct qualification leaf prints 17 central
declarations, all axiom-free.

## Central collapse receipts (10)

- `fixed_mint_iff_exact_entitlement_inhabited`
- `receiptsEverywhereGiveMint`
- `force_bearing_receipts_still_admit_total_mint`
- `contextErasedEntitlement`
- `erased_context_mints_previously_refused_crossing`
- `subjectErasedEntitlement`
- `erased_subject_mints_previously_refused_crossing`
- `admissible_consumer_need_not_use_receipt_identity`
- `rawCollapsedEntitlement`
- `unqualified_raw_bridge_enters_consumer`

## Central out-of-sample receipts (7)

- `witnessToAuthorityBridge`
- `distinct_claim_receipt_is_unavailable`
- `independent_authority_does_not_mint_cross_claim_entitlement`
- `admissibility_instance_refutes_receipt_free_mint`
- `exact_native_witness_yields_authority`
- `exact_native_authority_retains_books`
- `native_refusal_remains_local`

## Complete compiled footprint

- 591 compiled owned declarations across 13 selected PJ modules;
- 571 axiom-free;
- 20 exactly `[propext]`, inherited from pre-D-prime PJ modules;
- zero `Quot.sound`, `Classical.choice`, other, or mixed footprints;
- 38/38 D-prime declarations axiom-free;
- 17/17 named D-prime receipts axiom-free.

The public Admissibility core dependency separately exposes six printed
theorems, all axiom-free. Its declarations are not counted as PJ-owned.

Declaration-manifest SHA-256:
`5b4947101d4610fa86c536449e4eba399b601cf4c1b3cb396579d668b39f6e6a`.

No declaration was added to `PJ/Core.lean`. No source calculus or ratified
B-prime/C-prime proof was changed.
