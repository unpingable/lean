# PJ-2 — Governed Transport Fidelity Ledger

Date: 2026-07-22

## Disposition

`FAITHFUL-EDGE-LEVEL-INSTANTIATION`

The PJ adapter maps Governed Transport's translation and target-local
reliance rules into separate `PJ.IndexedJudgmentBridge` values. It preserves
the exact route witness and both endpoint bindings. It does not map the whole
GT law family into the PJ core, and it does not weaken that family to make the
adapter appear more complete.

## Authoritative source pins

The governing source object is the ratified GT scientific core frozen through
the GT-4A source-custody chain:

- GT-1 scientific candidate:
  `6a956cdba3409c1e8e0ea8f2abae858e2dba6b30`;
- GT-2 scientific candidate:
  `a76aee01f18a603814042c524ce9655db3521b87`;
- GT-3 custody activation:
  `e0fabffa0d3e840507aa342e80f1a662ad990aef`;
- GT-4A export candidate:
  `82918295ea7233ee5eda0a27070f1e0f507330ca`;
- GT-4A source-custody activation:
  `71714265062e3b45092c4d79927dfe2ed77dc5fa`;
- source-custody tree:
  `71cb93395a369ce4305288e15b55eb724da0814f`;
- frozen packet digest:
  `203f1b54a02469160aee8771a109db77fb812b5bdecd0036c66d066db570d08a`.

The frozen packet contains 704 declarations: 460 stable and 244 evidence.
Its recorded footprint is 679 axiom-free, 16 exactly `[propext]`, nine
exactly `[Quot.sound]`, zero other or mixed footprints, and zero
`Classical.choice`.

## Exact adapter imports

`PJ/Instances/GovernedTransport.lean` directly imports exactly:

```text
PJ.Core
Calculi.Scratch.GovernedTransport.Core
Calculi.Scratch.GovernedTransport.Positive
Calculi.Scratch.GovernedTransport.Negative
Calculi.Scratch.GovernedTransport.Hostile
```

`Hostile` is an evidence import used to carry exact native countermodels. It
is not treated as part of a stable compatibility interface. The adapter does
not import `All`, `Stage2`, `Stage3`, an instance aggregate, or a runtime
correspondence aggregate.

## Exact bridge mapping

### Translation receipt

`RouteReceipt bridge source target` contains:

- the native `Span.Witness`;
- equality binding the native source leg to `source`;
- equality binding the native target leg to `target`.

Endpoint equality alone cannot construct this receipt. The native route is
retained as data.

### Positive path

| Native GT edge | PJ value | Mapping |
|---|---|---|
| `TranslateAlong bridge SourcePositive ImportedPositive` | `positiveTranslationBridge` | source evidence plus exact `RouteReceipt` carries to the imported target artifact |
| `RelyLocally ImportedPositive TargetPositive` | `positiveRelianceBridge` | imported target artifact plus a same-target receipt carries to the target-local judgment |

`positiveEntitlementOfCertificateLift` shows that a native
`CertificateLift`, a native translation law, and the presented source
certificate construct an entitlement at the target selected by the retained
crossing witness. `positiveLocalEntitlementOfTranslated` constructs the
second entitlement only after the separate native reliance rule and its own
same-target receipt are available.

The adapter supplies no combined translation-and-reliance bridge.

### Negative path

| Native GT edge | PJ value | Mapping |
|---|---|---|
| `TranslateAlong bridge SourceNegative ImportedNegative` | `negativeTranslationBridge` | source-negative evidence plus exact `RouteReceipt` carries to imported negative evidence |
| `RelyLocally ImportedNegative TargetNegative` | `negativeRelianceBridge` | imported negative evidence plus a same-target receipt carries to the target-local negative judgment |

`negativeLocalEntitlementOfTranslated` preserves the second edge as a
separate entitlement. The positive and negative families are not collapsed
into a generic success/failure carrier.

## Exact hostile carry-through

### Missing positive lift

`MissingPositiveLiftAdapter.native_missing_lift_remains_not_entitled` retains
the complete native
`Hostile.MissingPositiveLift.source_witness_without_lift_does_not_transport`
packet:

- the source realization is inhabited;
- no certificate lift exists;
- no target realization exists.

Through the PJ adapter it additionally proves
`NotEntitledFrom () false` and `NotEntitledFrom () true`. A vacuous
translation function over the empty witness type does not manufacture a
route receipt.

### Target-local negative laundering

`TargetLocalNegativeAdapter.target_local_evidence_remains_not_entitled`
retains the complete native
`Hostile.TargetLocalRegression.target_local_block_cannot_masquerade_as_transport`
packet:

- target-local blockage is inhabited;
- transported blockage from the empty source-negative family is not.

The PJ conclusion is `NotEntitledFrom () false` for the negative translation
bridge. Independently inhabited target-local evidence therefore remains
distinct from source-relative entitlement.

## Local GT structure deliberately omitted from PJ

The adapter does not represent the following GT-specific law families as PJ
core fields:

- candidate and certificate coverage beyond the exact receipt used by one
  edge;
- `TargetCovered`, `ExhibitedGap`, coverage decisions, and coverage debt;
- image-relative versus global blockage upgrades;
- residue and refusal-recovery structure;
- pullback composition and end-to-end fibers;
- identity spans, leg-preserving equivalence, and associativity coherence;
- federation and jurisdiction tags;
- injective coverage extension and exact repair;
- C01, C02, C03, or C04 instance dispositions;
- NQ evaluation-history or any other runtime correspondence;
- authority, custody ownership, operational execution, spend, or a general
  debt algebra.

These omissions are classifications, not failed proofs. `PJ.Core` contains no
generic field forced to express them during PJ-1.

## No weakening finding

The mapped edges consume the same native evidence required by GT:

- translation consumes a native crossing witness and source artifact;
- both legs are explicitly bound to the PJ indices;
- target-local reliance remains a separate native rule;
- bare target inhabitation is not converted into source-relative
  entitlement;
- a missing route remains a missing entitlement;
- target-local negative evidence remains non-transported without source
  provenance.

No GT theorem, definition, endpoint, evidence family, or hostile model was
modified. No adapter premise replaces a native law with a Boolean or free
permission field.

## Declaration and axiom result

The adapter has 14 handwritten declarations:

- one exact receipt structure;
- 11 definitions;
- two hostile theorems.

All 13 value and theorem declarations are independently printed axiom-free.
`RouteReceipt` is an ordinary inductive data structure and introduces no
axiom. Direct compilation passed with:

```text
lake env lean PJ/Instances/GovernedTransport.lean
```

`git diff --check` also passed for the adapter.

## Claims not made

PJ-2 does not establish:

- that all GT structure belongs in a common cross-calculus core;
- generic bridge identity, composition, associativity, or coverage;
- a generic refusal, frontier, ownership, spend, or conservation theory;
- that translation itself authorizes target-local reliance;
- that target truth or target evidence implies source-relative entitlement;
- global blockage from image-relative negative transport;
- a standalone coverage-debt algebra;
- public promotion, runtime conformance, operational correspondence, or
  ownership transfer;
- any conclusion about Execution Custody, Someone Continuity, or the held-out
  StaticRole calculus.

The exact PJ-2 result is narrower: GT's native evidence-bearing translation
and reliance edges faithfully inhabit the minimal indexed bridge substrate,
and two load-bearing GT countermodels remain hostile after that mapping.
