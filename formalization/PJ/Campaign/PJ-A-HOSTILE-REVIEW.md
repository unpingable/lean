# PJ-A — Independent Hostile Review

Date: 2026-07-22

## Review result

`PRIMARY-ADAPTERS-CLEAN; CORE-LAWFULNESS-REMAINS-PER-ADAPTER`

The minimal PJ structure survives the required field-collapse attacks when
instantiated by the three primary calculi. It does not, by itself, certify
that every arbitrary inhabitant of `IndexedJudgmentBridge` is semantically
lawful. That limitation is real, bounded, and already made explicit by the
PJ-1 adapter qualification rule.

The independent reviewer inspected `PJ/Core.lean` and the Governed Transport,
Execution Custody, and Someone Continuity adapters without relying on the
author summaries. StaticRole remained held out from this independent primary
adapter review. No file was edited by the reviewer.

## Exact source pins reviewed

### Governed Transport

- GT-4A source-custody activation:
  `71714265062e3b45092c4d79927dfe2ed77dc5fa`
- activation tree:
  `71cb93395a369ce4305288e15b55eb724da0814f`
- frozen packet digest:
  `203f1b54a02469160aee8771a109db77fb812b5bdecd0036c66d066db570d08a`

### Execution Custody

- public revision:
  `9dca58f4587a4a4f5b724662b176af8de3040c04`
- public tree:
  `7e2b27939bafe7a214085112af2777e395b1b94f`
- source blob:
  `5b4b8d00700e8aea2fbe5c94d17e99cdc933a876`
- source SHA-256:
  `966d1f6f63d022b13a1ff031fe0558c99e6b2b304ba6f89550d632de14d18aef`

### Someone Continuity

- frozen source commit:
  `b00d76535ab6848eb2db80cb68601a07b118c4ef`
- frozen source tree:
  `8c7e42e8c97659763e5573d063a54fb1d5af1d45`
- `Someone.lean` blob:
  `80a71ce18e55515a97567cc9d9f162fd23998ff7`
- qualification candidate:
  `cc84f4b9a2bb85eda4942d13fb1696e3d44a45a3`
- operator ratification:
  `99f3973aca420817ac4eb5a5a1282252326c32e7`

The PJ core under attack had SHA-256:
`1d86bee97f92f2644d8605a05d6a31deaa3584f55582d4a09b638718ffff185c`.

## Core triviality attack

`IndexedJudgmentBridge` is a raw substrate, not a proof that every instance
is honest. A dishonest inhabitant can choose, for example:

```text
Receipt source target := TargetJudgment target
carry receipt _ := receipt
```

or choose `Receipt := Unit` with a constant `carry` that ignores source
evidence whenever the target family is already inhabited.

Adding a field such as `lawful := true` or a proof that merely restates the
desired conclusion would not repair this; it would store the theorem PJ is
supposed to earn. The admissible architecture is therefore the one recorded
in `PJ-1-SIGNATURE-LEDGER.md`: the core provides the typed source, target,
receipt, and consumption shape, while each adapter must independently prove
that its receipt and carry are exact native structures and retain a native
hostile boundary.

Consequently, PJ-A may claim that its *qualified adapters* are lawful. It may
not claim that arbitrary inhabitants of the structure are licensed bridges.

## Field-collapse attacks

| Attack | Exact failure exposed |
|---|---|
| remove or collapse endpoint indices | erases exact GT source/target legs, the complete Execution stage, and full Someone agents |
| replace receipt with `Unit` | makes the GT missing-route hostile, Execution constructor side conditions, and arbitrary-endpoint Someone reachability undefinable |
| remove source evidence | permits a receipt or independently inhabited target to mint target entitlement |
| replace receipt by target evidence | stores the target conclusion instead of licensing its derivation |
| remove `carry` | leaves vocabulary and packaging but no theorem-producing common structure |
| add generic composition | manufactures a law not forced by Execution Custody and not present in the PJ-A core |
| add a generic refusal sum | collapses GT negative evidence, Execution refusal/unknown, and Someone proposition-level nonreachability |

The three qualified adapters use every retained core field. No generic
composition law, refusal sum, owner, authority, spend, frontier, or
context-transport theorem is smuggled through an adapter.

The synthetic control in `PJ/Hostile.lean` was also hardened before freeze.
Its source and target judgments carry index-bound observed values; its receipt
is exact endpoint equality; and its `carry` transports the source observation
through that equality.  The positive control therefore consumes both source
evidence and receipt.  Separate hostiles show that independently inhabited
source and target judgments do not provide a mismatched receipt, and that a
receipt cannot be replayed from the wrong source.  The fixture no longer uses
`Unit` as an output or an evidence-ignoring carry.

## Governed Transport attack result

`PJ/Instances/GovernedTransport.lean` is clean at its declared edge-level
scope:

- `RouteReceipt` stores only a native `Span.Witness` and exact source and
  target leg equalities;
- translation consumes both the crossing witness and exact source artifact;
- target-local reliance remains a second bridge with a separate same-target
  receipt;
- the missing-positive-lift hostile still defeats entitlement;
- target-local negative evidence still cannot masquerade as transported
  negative entitlement;
- no composition, coverage globalization, exact repair, or target authority
  is manufactured.

The limitation is load-bearing: this is a faithful edge-level common reduct,
not a preservation theorem for the entire ten-module GT law family. GT
coverage, residue, composition, coherence, repair, and federation remain
local structures and cannot be cited as generic PJ-A results.

## Execution Custody attack result

`PJ/Instances/ExecutionCustody.lean` is clean:

- every bridge retains the complete `ExecutionStage` endpoint through exact
  equality;
- additional receipt fields are exactly the premises of the corresponding
  native constructor;
- every `carry` consumes its named source judgment;
- `DidNotExecute` and `CommitUnknown` remain different target families with
  incompatible outcome receipts;
- all six source non-collapse boundaries remain visible, including unknown
  testifying to neither execution nor refusal;
- no trajectory composition, actuator causality, reconciliation, ticket
  replay, or one-use theorem is introduced.

The adapter therefore preserves a bounded single-stage calculus. It does not
upgrade asserted stage fields into operational execution correspondence.

## Someone Continuity attack result

`PJ/Instances/SomeoneContinuity.lean` is clean:

- every bridge receipt is the exact native `Reachable source target` proof;
- each carry invokes the corresponding native preservation theorem with the
  exact source evidence;
- the complete `Agent` endpoints remain indexed;
- `AgentId` preservation remains a separate local theorem and is not renamed
  authentication;
- foreign-packet nonreachability defeats entitlement through the exact native
  receipt;
- reachability identity and composition remain instance-local.

The adapter remains bounded to identity-bound continuity admission on the
reachable fragment. It does not add retained route identity, transition
history, durable revocation, substrate rebinding, authenticated identity, or
typed refusal.

The audit found six axiom-free and seven exactly `[propext]` declarations in
this adapter. Those seven dependencies are inherited through the exact source
preservation and anti-entitlement proofs; PJ introduces no new axiom class.

## Compilation and axiom result

The independent reviewer compiled:

```text
PJ/Core.lean
PJ/Instances/GovernedTransport.lean
PJ/Instances/ExecutionCustody.lean
PJ/Instances/SomeoneContinuity.lean
```

All compiled successfully. Printed declarations were axiom-free except for
the exact seven inherited `[propext]` footprints in the Someone adapter. No
`Classical.choice`, `Quot.sound`, custom axiom, or mixed PJ-added footprint was
found in the reviewed declarations.

## Hostile conclusion

No primary adapter weakens its source calculus, erases a load-bearing refusal
or non-implication, forgets an exact endpoint, or fills a locally missing
bridge. The common core remains intentionally small and admits degenerate
unqualified inhabitants; therefore semantic lawfulness is earned by the
adapter qualification packet, not by structure inhabitation alone.

This result supports Tranche-A candidacy only at the qualified
indexed-judgment/receipt substrate level. It does not yet establish a generic
illegal-lift theorem, generic composition, frontier preservation,
institutional ownership, or a Planet classification.
