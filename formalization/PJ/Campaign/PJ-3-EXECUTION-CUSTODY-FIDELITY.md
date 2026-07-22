# PJ-3 Execution Custody Fidelity Ledger

Date: 2026-07-22

This ledger records the Tranche-A PJ adapter for the exact public Execution
Custody calculus. It is an instantiation record, not a promotion, rewrite, or
claim that PJ supplies execution semantics.

## Frozen public source

| Property | Exact value |
|---|---|
| repository | `/home/jbeck/git/lean` |
| pinned revision | `9dca58f4587a4a4f5b724662b176af8de3040c04` |
| pinned tree | `7e2b27939bafe7a214085112af2777e395b1b94f` |
| source path | `LeanProofs/BoundedCalculi/ExecutionCustody.lean` |
| source blob | `5b4b8d00700e8aea2fbe5c94d17e99cdc933a876` |
| source SHA-256 | `966d1f6f63d022b13a1ff031fe0558c99e6b2b304ba6f89550d632de14d18aef` |
| public custody | `PUBLIC-SHIPPED` |
| public surface role | `STABLE-SURFACE` |
| release lineage | v3.0.0, Bounded Lifecycle Calculi |

PJ imports that source through
`LeanProofs.BoundedCalculi.ExecutionCustody`. It does not copy or edit the
public module. The source's explicit limits remain binding: `commitSent` and
`outcome` are independent asserted fields, and the module proves a
single-stage ticket flip rather than trajectory-level linearity.

## Exact bridge surface

Every adapter bridge uses the complete native `ExecutionStage` as both index
types. Its receipt contains `source = target`; additional constructor premises
remain exact evidence at that source stage. There is one PJ bridge for each of
the eight native constructor edges.

| PJ bridge | Source judgment | Exact additional receipt evidence | Target judgment |
|---|---|---|---|
| `ticketFreshToMayAttempt` | `TicketFresh` | same-stage equality | `MayAttempt` |
| `mayAttemptToMayCommit` | `MayAttempt` | `LocalPreconditions` | `MayCommit` |
| `mayCommitToCommitAttempted` | `MayCommit` | `TicketConsumed` and `commitSent = true` | `CommitAttempted` |
| `commitAttemptedToDidExecute` | `CommitAttempted` | `outcome = succeeded` | `DidExecute` |
| `commitAttemptedToDidNotExecute` | `CommitAttempted` | `outcome = refused` | `DidNotExecute` |
| `commitAttemptedToCommitUnknown` | `CommitAttempted` | `outcome = unknown` | `CommitUnknown` |
| `didExecuteToPreservedSafety` | `DidExecute` | `safetyWitness = true` | `PreservedSafety` |
| `obligationReceiptToDischargedObligation` | `obligationReceipt = true` | same-stage equality | `DischargedObligation` |

The final edge deliberately does not invent a safety premise. The native
discharge constructor consumes only the obligation-receipt field, so PJ does
the same.

The eight evidence objects `freshTicketEntitlement`,
`checkedAttemptEntitlement`, `commitAttemptEntitlement`,
`successfulExecutionEntitlement`, `refusedOutcomeEntitlement`,
`unknownOutcomeEntitlement`, `safetyEntitlement`, and
`dischargeEntitlement` exercise the eight exact carries. An entitlement is a
Type-valued evidence object in the PJ core; it is not flattened into a Boolean
or bare target proposition.

## Non-collapse and outcome fidelity

The adapter carries the source countermodels through
`IndexedJudgmentBridge.NotEntitledFrom`, while retaining the corresponding
native negative judgment where one exists.

| Adapter theorem | Retained boundary |
|---|---|
| `may_attempt_not_entitled_to_commit_without_local_preconditions` | `MayAttempt` holds; `MayCommit` does not; no exact bridge receipt exists |
| `may_commit_not_entitled_to_attempt_without_send` | `MayCommit` holds; neither `CommitAttempted` nor `DidExecute` holds; no send receipt exists |
| `refused_attempt_entitled_to_refusal_not_execution` | ticket is spent and refusal is entitled; execution and unknown are not entitled |
| `unknown_attempt_entitled_to_neither_outcome` | unknown is entitled; neither execution nor refusal holds or is entitled |
| `execution_not_entitled_to_safety_without_witness` | execution holds; safety does not; no safety-witness receipt exists |
| `safety_does_not_supply_discharge_receipt` | safety holds; discharge does not; safety supplies no obligation receipt |

`DidNotExecute` and `CommitUnknown` therefore remain different target families
with incompatible exact outcome receipts. PJ does not replace them with a
generic failure sum, turn unknown into negation, or permit either outcome to
testify as execution.

## Local structure deliberately omitted

The minimal PJ core and this adapter do not absorb:

- ticket identity, freshness policy, or trajectory-level one-use semantics;
- actuator causality or a claim that a sent commit caused the recorded outcome;
- owner, authority, permit, epoch, atomicity, or reconciliation structure;
- receipt identity or persisted operational custody;
- generic bridge composition or a synthetic direct `MayCommit → DidExecute`
  bridge;
- a universal refusal/unknown carrier;
- generic safety, obligation, spend, or conservation laws;
- the later custody-indexed execution-sequent family.

Those omissions preserve the source boundary. They are not silently supplied
as PJ assumptions.

The Skunkworks `RuntimeContracts` portfolio is excluded. It is returned and
unratified, is not a PJ forcing source, is not imported by this adapter, and
cannot supplement missing Execution Custody semantics.

## Declaration and axiom result

The adapter file is `PJ/Instances/ExecutionCustody.lean`.

- 29 authored top-level declarations:
  - two receipt structures;
  - five exact-premise families;
  - eight native bridge instances;
  - eight positive entitlement objects;
  - six non-collapse theorems.
- 14 central declarations are independently printed in the adapter:
  - eight positive entitlement objects;
  - six hostile/non-collapse theorems.
- all 14 printed declarations are axiom-free;
- no `sorry`, custom axiom, `Classical`, `Classical.choice`, `Quot`, Mathlib,
  unsafe declaration, or partial declaration is used.

Verification performed:

```text
lake build PJExecutionCustodySources
lake env lean PJ/Instances/ExecutionCustody.lean
git diff --check -- PJ/Instances/ExecutionCustody.lean
```

The public-source target built in three jobs, the adapter compiled, every
printed declaration reported no axioms, and the whitespace check passed.

## Fidelity disposition

`EXACT-INSTANCE-WITH-LOCAL-EXECUTION-STRUCTURE-OMITTED`

No source judgment, refusal distinction, unknown distinction, stage index,
constructor premise, or published non-collapse wall was weakened. PJ records
only licensed same-stage carries. Bare target inhabitation remains distinct
from entitlement derived from source evidence plus the exact native receipt.

This result does not claim runtime execution, actuator conformance, effect
observation, trajectory-level spend, or a universal execution algebra.
