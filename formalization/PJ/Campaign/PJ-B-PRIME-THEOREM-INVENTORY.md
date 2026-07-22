# PJ Tranche B-prime Theorem Inventory

Date: 2026-07-22

## Generic surface added over frozen PJ-A

`PJ/Core.lean` is unchanged. Tranche B-prime adds these bounded generic
constructions:

- `AdmissibleConsumer`: a consumer whose only force-bearing entry point
  requires exact `EntitledFrom` evidence;
- `AdmissibleConsumer.consumeEntitled`: invokes the receipt-gated operation
  only with a native PJ-A entitlement;
- `ReceiptFreeMintAt`: the challenged total lift from source evidence plus
  independent target truth to exact source-relative entitlement;
- `ReceiptFreeMinter`: the stronger purported uniform lift across arbitrary
  bridge values;
- `EntitlementProjection`: an explicitly lossless presentation/recovery pair.

The central statement is:

```lean
theorem exact_receipt_prevents_target_minting
    {bridge : PJ.IndexedJudgmentBridge}
    {source : bridge.SourceIndex} {target : bridge.TargetIndex}
    (sourceEvidence : bridge.SourceJudgment source)
    (targetEvidence : bridge.TargetJudgment target)
    (receiptRefusal : bridge.NotEntitledFrom source target) :
    ReceiptFreeMintAt bridge → False
```

The scientific result is the theorem family, not this eliminator in
isolation. `no_uniform_receipt_free_minter` supplies an inhabited exact-index
countermodel; `collapsed_bridge_admits_receipt_free_mint` constructs the
forbidden operation after replacing the dependent receipt family with
`Unit`; and `native_receipt_erasure_has_no_left_inverse` proves that a
force-bearing receipt distinction cannot be recovered after erasure.

## Direct qualification set

All 32 named declarations below are axiom-free.

### Generic and hostile declarations (11)

- `AdmissibleConsumer.consumeEntitled`
- `exact_receipt_prevents_target_minting`
- `EntitlementProjection.present_injective`
- `Hostile.wrong_context_remains_not_entitled`
- `Hostile.wrong_subject_remains_not_entitled`
- `Hostile.no_uniform_receipt_free_minter`
- `Hostile.exact_receipt_is_sufficient_for_bounded_consumer`
- `Hostile.distinct_native_bridges_have_distinct_force`
- `Hostile.wrong_native_bridge_remains_not_interchangeable`
- `Hostile.collapsed_bridge_admits_receipt_free_mint`
- `Hostile.native_receipt_erasure_has_no_left_inverse`

### Primary specializations (17)

- GT: five declarations covering the exact omitted route, non-vacuity,
  positive recovery, anti-minting, and bounded consumption;
- Execution Custody: seven declarations covering cross-stage refusal,
  same-stage native refusal, exact recovery, outcome-lane separation,
  anti-minting, and bounded consumption;
- Someone Continuity: five declarations covering cross-agent refusal,
  independent packet truth, exact reachable-fragment recovery,
  anti-minting, and bounded consumption.

### Held-out StaticRole declarations (4)

- `faithfulR3Consumer`
- `exact_static_role_receipt_is_sufficient`
- `r2_truth_does_not_mint_r3_entitlement`
- `functional_dependence_remains_local`

## Load-bearing laws

- Context and subject are actual dependent indices, not copied metadata.
- Native receipt families differ with the actual bridge value.
- Exact index equality defeats wrong-context and wrong-subject minting.
- Native `carry` derives target evidence from source evidence plus receipt.
- Recovery-after-presentation yields injectivity; removing recovery removes
  that conclusion.
- Collapsing the receipt family to `Unit` makes receipt-free minting
  constructible.

The theorem does not establish runtime enforcement, cryptographic
unforgeability, constructor privacy, universal adapter lawfulness, ownership,
composition, or a residual algebra.
