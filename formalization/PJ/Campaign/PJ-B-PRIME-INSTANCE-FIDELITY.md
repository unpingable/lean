# PJ Tranche B-prime Instance Fidelity

Date: 2026-07-22

## Governed Transport

The specialization uses the native `CompositionDebt.first` span. Source
evidence and target evidence at `true` are both inhabited, but the exact span
has only the `false` route. `CompositionDebt.repairedFirst` is a genuinely
different bridge that reaches `true`; its receipt cannot repair the original
bridge's omission. The covered `false` route remains positively consumable.

This is the faithful GT result available in the frozen PJ-A source surface.
That source does not formalize a Lean-to-Rust runtime-conformance judgment, so
B-prime does not invent one and does not claim runtime correspondence.

## Execution Custody

The specialization retains the complete `ExecutionStage` index. Both
`MayCommit commitNotAttemptedStage` and
`CommitAttempted successfulCommitStage` are inhabited, but the native
same-stage receipt cannot cross between those distinct states. The stronger
native same-stage wall also remains: permission without send/consumption does
not yield attempt or execution entitlement.

Exact same-stage evidence remains sufficient. `CommitUnknown`,
`DidExecute`, and `DidNotExecute` remain separate. B-prime does not make
permits reusable, identify attempt with commit, or absorb local state/spend
semantics into PJ.

## Someone Continuity

Both John and Gwen's initial states satisfy native `OwnsPacket`. Native
`Reachable` preserves exact `AgentId`, so local packet truth for Gwen cannot
mint John-to-Gwen continuity entitlement. John's exact admitted reachable
fragment remains positively consumable.

The result is limited to the ratified Someone calculus. It does not claim
authentication, durable operational history, runtime continuity, or
correspondence with the operational Continuity repository. A future public
transfer must still rename the public module and namespace to `Continuity`
through a separate exact gate.

## Held-out StaticRole

StaticRole remains a faithful partial specialization. An exact
faithful-presentation R2-to-R3 entitlement feeds a proof-retaining consumer.
R2 and a faithful R3 judgment can both be inhabited while the distinct
neutralizing-presentation bridge remains unentitled. Thus target truth under
one lawful wiring does not repair another bridge's receipt gap.

This is a wrong-wiring anti-entitlement boundary, not the same-bridge
inhabited-target hostile used by the three primary specializations.
Presentation, evaluation, de-se erasure, output discrimination, and failure
of factorization remain StaticRole-local. No such field enters the PJ core or
B-prime generic theorem.

## Fidelity disposition

All three primary instances produce meaningful native anti-minting
specializations without changing PJ-A. The held-out result preserves its
local functional-dependence extension. No local refusal, unknown lane,
identity index, or exact route is weakened.
