# Governed computation: a plain-language orientation

This repository is a formal study of **governed computation**. It asks when
available evidence justifies a conclusion or state transition, and which
additional conditions remain independent: standing, custody, authority,
resource spend, refusal, obligation, origin, and retained history.

This is theoretical computer science and formal methods applied to systems
whose decisions have consequences outside the checker. Lean machine-checks
the definitions and theorems. It does not turn the formal model into a claim
that a particular institution or runtime implements it.

## Why reachability is not enough

A transition system can establish that a state is reachable. A proof object
can establish that a proposition follows from assumptions. Governed systems
often need more information than either answer carries by default:

- Which exact claim did the evidence support?
- Was the actor entitled to originate or exercise that judgment?
- Who held the relevant object or decision, and under what custody?
- Was a one-use resource consumed?
- Was the result accepted, refused, or left unknown?
- Did the action create an obligation that is still live?
- Did a later projection preserve the source, route, origin, and prior
  decision, or silently recompute a more convenient answer?

The formal models keep these questions separate. A theorem may relate two of
them, but shared vocabulary or a successful endpoint does not supply that
theorem for free.

## The three V15 primary domains

V15's Cross-Calculus Atlas records selected correspondences among three
independently defined domains.

1. **Governed Transport (GT)** formalizes evidence carried across a typed
   span. Its V15 adapter maps four edge shapes: positive and negative
   translation, and the separate positive and negative target-local reliance
   steps. A translation receipt contains the native route witness and both
   endpoint bindings. The adapter does not map the whole GT law family or
   combine translation with reliance.
2. **Execution Custody** distinguishes ticket freshness, permission to
   attempt, permission to commit, a sent commit, success, refusal, unknown
   outcome, safety evidence, and obligation discharge. Its V15 adapter maps
   eight native constructor edges. Every edge retains the complete
   `ExecutionStage`; additional premises such as local preconditions, ticket
   consumption, outcome, safety, or discharge receipts remain explicit.
3. **Continuity Admission** establishes identity-bound continuity admission
   on a reachable fragment. Its three V15 edges preserve well-formedness,
   coherence, and packet ownership along the native `Reachable` receipt. The
   asserted agent identifier is preserved, not authenticated. The private
   excavation name was `Someone.lean`; `Continuity.Admission` is the sole
   authoritative public module.

Each bridge's carry function is total once its declared source evidence and
exact receipt are supplied. That does **not** mean every source has a receipt,
that arbitrary bridges are qualified, or that the three calculi are mutually
translatable. StaticRole is a held-out partial instance: its R0–R3 edges fit
the minimal receipt-indexed substrate, while its functional-dependence theory
remains local.

## What the Atlas establishes

PJ is the small common substrate used to record these selected mappings. A PJ
bridge names source and target index types, source and target judgments, an
exact receipt family, and a carry operation. Entitlement packages the source
evidence with that exact receipt.

The checked V15 adapters preserve the native indices and the receipt evidence
needed by their mapped edges. They also retain source-local countermodels. The
exact-receipt anti-minting result proves that, at an index pair where source
and target judgments are both inhabited but entitlement is refuted, no
receipt-free function can manufacture that entitlement from the two bare
judgments. This is adapter-local and source-relative. It is neither a generic
bridge-qualification theorem nor a cryptographic claim.

The final classification is `ATLAS`, with four first-class negative results:

- `FRONTIER-NOT-COMPOSITIONAL`;
- `NO-USEFUL-OWNERSHIP-COMMONALITY`;
- `CONTEXT-TRANSPORT-NOT-GENERIC`; and
- `ONLY-DOMAIN-SPECIFIC-RESIDUAL-THEORIES`.

V15 therefore does not establish a shared bridge algebra, generic frontier
composition, generic ownership, generic context transport, or a universal
calculus. Inquiry and Preparation remain frozen independent comparison-only
neighbors outside the PJ primary surface.

## What this is not

The repository is not specifically:

- a blockchain or cryptocurrency protocol;
- a zero-knowledge system;
- a legal-evidence or discovery product, or a legal protocol;
- a smart-contract framework;
- a generic audit-log implementation;
- a category-theory library; or
- an alternate-reality game or deliberately theatrical verification artifact.

It is also not a claim that all institutional processes reduce to one
calculus. All source and verification commands are public; campaign records
are provenance and scope control, not a withheld or interactive reveal.

Any of those areas could supply an application or model, but none is the
subject that defines the project. “Receipt” is proof-relevant justification,
not a transaction receipt; “custody” is a formal responsibility relation, not
necessarily evidentiary chain-of-custody; and “Atlas” names a collection of
bounded mappings, not a categorical equivalence.

## A bridge to standard terminology

| Term | Meaning in this repository |
| --- | --- |
| `Witness` | Evidence indexed by the exact claim and sufficient for that claim's native positive judgment. It is more specific than arbitrary proof data. |
| `Refusal` | Structured evidence, also indexed by the claim, recording why a total checker did not admit it. It is not merely `false`. |
| `Standing` | Entitlement to participate in or originate a judgment. Standing can coexist with refusal. |
| `Custody` | Responsibility for holding or preserving an object, receipt, or decision. Custody can coexist with lack of authority. |
| `Spend` | A consumable capability or resource required by a specific native transition. It is not a universal currency shared by all families. |
| `Obligation` | An unresolved consequence left by an action. Safety, success, and discharge remain separate judgments. |
| `Stored decision` | A retained witness-or-refusal result from one evaluation. Downstream projections use that result rather than reevaluating the native claim. |
| `Hostile countermodel` | A proved or executable model chosen to make an invalid implication tempting while one load-bearing condition is absent. |
| `Anti-minting` | A non-implication or invariant showing that evidence, authority, entitlement, or discharge cannot appear without its required source structure. |

These are orientation bridges, not synonyms for capabilities, effects, traces,
transition labels, or generic proof objects.

## Why “hostile countermodel” is a technical term

The adjective means that the model is constructed adversarially against a
proposed implication. The countermodel changes or withholds one exact premise
while preserving enough nearby structure to expose a semantic collapse.

Three public examples are:

- [`custody_does_not_grant_dynamic_authority`](../LeanProofs/Admissibility/Calculus/Instances/BoundedPaidReachability.lean#L181):
  the bare reachability claim has custody but a refusal, so custody does not
  create authority;
- [`may_attempt_not_entitled_to_commit_without_local_preconditions`](../formalization/PJ/Instances/ExecutionCustody.lean#L191):
  attempt permission exists while commit permission and the exact bridge
  receipt do not; and
- [`safety_does_not_supply_discharge_receipt`](../formalization/PJ/Instances/ExecutionCustody.lean#L284):
  preserved safety exists while obligation discharge and its receipt do not.

These are negative scientific results. They are not missing features, attack
branding, or a promise that a generic theorem will appear later.

## One concrete walkthrough: bounded BreakGlass

The bounded BreakGlass instance shows why the vocabulary cannot be flattened
to “valid state transition.” It is relative to consumer-supplied atoms:
origin, state, actor, and step.

1. **Proposed transition.** A claim pairs a lifecycle origin with one phase:
   prospective, attempted, committed, settled, ordinary laundering, or audit
   laundering. The last two are claims about how the exceptional path should
   be classified, not lifecycle progress.
2. **Evidence.** Each admitted phase has a different claim-indexed witness. A
   settled witness contains the exact origin match, native commit, and native
   reconciliation relation. A copied phase name alone is insufficient.
3. **Standing, custody, and authority.** The instance has separate standing
   and custody books. Authority means that the exact phase witness exists;
   neither book constructs that witness. Settlement standing, for example,
   can coexist with refusal of a falsely clean audit history.
4. **Consumptive step.** At the prospective phase the native permit token is
   in `availablePermits`; after the attempt it is in `usedPermits` and the
   pending attempt is recorded. This is the instance's concrete one-use
   control, not a generic PJ `Spend` operation.
5. **Acceptance or refusal.** The total checker admits the four native phases
   at the matching origin. It returns structured refusal for a foreign origin,
   false ordinary authorization, or false audit cleanliness.
6. **Remaining obligation.** There is no live obligation before commit.
   [`commit_opens_exact_obligation`](../LeanProofs/Admissibility/Calculus/Instances/BreakGlass.lean#L316)
   opens one origin-qualified obligation, and
   [`settlement_closes_exact_obligation`](../LeanProofs/Admissibility/Calculus/Instances/BreakGlass.lean#L320)
   closes that exact obligation.
7. **Origin and stored history.** The claim retains its lifecycle origin
   through authority; a foreign-origin twin at the same phase is refused. The
   audit entry remains in the settled ledger, so settlement cannot be replayed
   as “ordinary” or “clean.” In the public crossing, the native BreakGlass
   outcome is stored once and later verdict, location, refusal, origin, and
   obligation observations are projected from it rather than recomputed.

The example proves a bounded lifecycle and its separations. It does not prove
runtime attestor honesty, unique origin allocation, a general emergency
process semantics, or a generic discharge/payment theory.

## Recurring failure shapes

- **Laundering:** a conversion drops the evidence trail and makes an assertion
  appear stronger than its source.
- **Stale reliance:** evidence is no longer licensed for one use even if it is
  not false.
- **Endpoint judgment:** two states look the same while only one has a lawful,
  paid history.
- **Re-deciding until convenient:** a checker is invoked repeatedly instead
  of retaining its original witness or refusal.
- **Exceptional-path laundering:** special authority is presented as ordinary
  authority, or settlement is presented as clean history.

## Scope and status

The repository is axiom-classified, not axiom-free. Exact dependency,
declaration, axiom, hostile-fixture, and changed-path reports are retained in
the release ledgers and qualification receipts. A green Lean build establishes
the stated mathematics under those disclosed assumptions. It does not
establish runtime conformance, attestor honesty, cryptographic security,
operational AG/NQ realization, a JCP implementation, consciousness,
phenomenology, or metaphysical personal identity.

V15 is operator-ratified release preparation at version `15.0.0`; it has no
v15 tag or version DOI and is not yet the published release. The current
published release remains v14.0.0.

## Where to go next

- [`../README.md`](../README.md) — build commands, release state, and reading
  paths by audience.
- [`../WHAT-THIS-PROVES.md`](../WHAT-THIS-PROVES.md) — technical,
  claim-by-claim scope.
- [`V15-PUBLIC-INDEX.md`](V15-PUBLIC-INDEX.md) — exact V15 module and adapter
  map.
- [`V15-PUBLIC-HOSTILE-AUDIT_2026-07-22.md`](V15-PUBLIC-HOSTILE-AUDIT_2026-07-22.md)
  — representative collapse ledger and formal pins.
- [`calculus/README.md`](calculus/README.md) — v14 conceptual, mathematical,
  and Lean-reference entrances.
- [`../CLAIM-REGISTER.md`](../CLAIM-REGISTER.md) — audited SOUND / BROKEN /
  STALE / OPEN claims.
