# Governed computation: a plain-language orientation

Start with four failures. None of them is hypothetical in kind; each is a
standing pattern in deployed systems:

- A credential was revoked an hour ago, but a service still accepts it —
  the token parses, the signature checks, and nothing in the request carries
  the revocation.
- A client retries a failed call, and the retry replays yesterday's approval
  as though it were granted fresh today.
- A pipeline promotes a build because the target state is reachable, without
  asking whether the actor pushing it had the right to originate that change.
- An emergency override runs, settles correctly — and then the audit trail
  reads as if the ordinary process had been followed all along.

In every case the system lands in a *plausible state* for an *unjustified
reason*. Endpoint-focused verification does not catch this unless
justification is modeled explicitly: model checking asks whether a bad state
is reachable, and program logic asks whether outputs meet a spec, and in
each failure above the endpoint state is fine and the output is correct.
What is broken is the **justification**: who was entitled, on what evidence,
at what cost, with what left owing. Those conditions *can* be encoded into
an enriched state or a temporal specification — nothing prevents it — but
they usually are not, and each ad-hoc encoding re-decides from scratch what
counts as evidence, authority, or an outstanding duty.

Modeling them explicitly, once, with types and theorems, is this
repository's subject. Each justification condition gets its own formal type
in Lean 4 — evidence, standing, custody, authority, spend, refusal,
obligation, origin, retained history — and Lean machine-checks which
inferences between them are valid and which are refuted by explicit
countermodel.

## An entry metaphor: the secure courier

One scaffold, to make the vocabulary land — this is an entry ramp, not a
definition, and the [guardrails table](../README.md#semantic-guardrails)
gives the exact boundaries:

| Courier world | Formal object | The question it answers |
| --- | --- | --- |
| The package contents | `Witness` (evidence) | Does the evidence support *this exact claim*? |
| The sender's right to ship at all | `Standing` | May this actor even originate the request? |
| The courier cleared for this route | `Authority` | Is this judgment actually licensed here? |
| An unbroken chain of hands | `Custody` | Was the thing held intact the whole way? |
| The one-use shipping label | `Spend` | Was a consumable resource actually consumed? |
| The signature on delivery | `Receipt` | What exact evidence did this step produce? |
| "Refused: address unknown" slip | `Refusal` | *Why* was it not admitted — as data, not a crash? |
| Customs duty owed after delivery | `Obligation` | What does the action leave outstanding? |
| The tracking history | Origin / stored history | Can the past be replayed or rewritten as fresh? |

The point of the formalization is that **none of these rows implies
another**. Delivery does not prove the duty was paid. An intact chain of
hands does not prove the courier was cleared for the route. The theorems in
this repository prove exactly which crossings between rows are valid, and
the countermodels show each tempting invalid crossing failing.

Concretely, the machine-checked results include: custody does not create
authority; permission to attempt does not create permission to commit; an
observed-safe execution does not discharge the obligation it opened; a
replayed decision is not a fresh one; and an emergency settlement cannot be
read back as clean ordinary history. Each is a named theorem or countermodel
linked later in this document.

This is theoretical computer science and formal methods applied to systems
whose decisions have consequences outside the checker. Lean machine-checks
the definitions and theorems. It does not turn the formal model into a claim
that a particular institution or runtime implements it.

## The questions a reachability answer does not carry

A transition system can establish that a state is reachable; a derivation can
establish that a proposition follows from assumptions. Governed systems need
answers that neither carries by default:

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

1. **Governed Transport (GT)** starts with a proof-relevant `Span`, but that
   bare crossing geometry has no preservation or authority law. Separate
   `CandidateLift` / `CertificateLift`, `TranslateAlong`, and `RelyLocally`
   types state whether an artifact can enter a route, what is translated, and
   whether the target may use the imported artifact as a local judgment. Its
   V15 adapter maps four edge shapes: positive and negative translation, and
   separate positive and negative reliance. A route receipt retains the
   crossing witness and both endpoint bindings. The adapter does not map the
   whole GT law family, combine translation with reliance, or invent generic
   authority, custody, spend, or obligation fields absent from GT.
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

The checked V15 adapters preserve the native indices and the semantic receipt
required by each mapped edge. A PJ `Receipt` is an instance-supplied dependent
family indexed by source and target; its concrete content differs across GT,
Execution Custody, and Continuity Admission. These receipts are not inherently
signed, hashed, tamper-proof, zero-knowledge, or blockchain-backed.

The exact-receipt anti-minting result proves one precise prohibition. At an
index pair where source and target judgments are both inhabited but
`EntitledFrom` is refuted, no `ReceiptFreeMintAt` function can manufacture the
missing source-relative entitlement from the two bare judgments. It does not
claim that evidence, standing, custody, spend, discharge, closure, historical
identity, or origin support can never be minted under every other calculus;
those require their own typed result. This theorem is adapter-local and
source-relative, not generic bridge qualification or cryptographic
unforgeability.

The final classification is `ATLAS`, with four first-class negative results:

- `FRONTIER-NOT-COMPOSITIONAL`;
- `NO-USEFUL-OWNERSHIP-COMMONALITY`;
- `CONTEXT-TRANSPORT-NOT-GENERIC`; and
- `ONLY-DOMAIN-SPECIFIC-RESIDUAL-THEORIES`.

V15 therefore does not establish a shared bridge algebra, generic frontier
composition, generic ownership, generic context transport, or a universal
calculus. Inquiry and Preparation remain frozen independent comparison-only
neighbors outside the PJ primary surface.

## What V16 adds: does this view carry enough to decide?

V16 asks a narrower question about the same material, and it can be stated
without the vocabulary above. A decision needs some fact about a system — call
that fact the **target**. What the decider actually has is rarely the whole
system; it is a **view** of it: a summary, a projection, a forwarded record,
whatever survived the trip. Does the view carry enough?

Made precise: is there one rule that reads only the view and returns the right
target value, for every possible state of the system? When there is, the target
*factors through* the view. When there is not, no downstream transformation
derived solely from that view repairs it; independent enrichment supplies a
different input.

Four general results are proved:

- Chaining two sufficient views stays sufficient.
- A sufficient view never assigns one view value to two different target
  values — it lines up with the fibre-constancy relation already formalized
  elsewhere in the repository.
- If two states look identical in the view but differ in the target, the view
  is insufficient. One such collision settles it.
- Post-processing an insufficient view cannot restore sufficiency.
  Reformatting, recombining, or enriching it with anything already derivable
  from it does not add what was never there.

The converse is deliberately not claimed. Showing that a view never conflates
two target values does not by itself hand you the rule that reads it back;
constructing that rule needs lifting data the general setting does not supply.

Alongside the general results, one fully enumerated finite example computes
exactly which coordinate selections determine a chosen target, and five small
fixtures each exhibit one concrete way a view falls short: a policy that
refuses inspection, one record read in two different contexts, a capacity
constraint whose schedule cannot be realized, an unobservable link between
events, and a hidden relation that two worlds disagree on while agreeing
everywhere visible.

These are standard facts about functions and views, plus an exhaustive
calculation over a fixed table. No new mathematics is claimed; the work is
stating them precisely and machine-checking them together. Each fixture is
bounded to itself — the authorization one is not a theory of authorization,
and the hidden-relation one is not a claim about physical truth or causation.
V16 adds public evidence only. It promotes no stable surface, and the V15
`ATLAS` classification above is unchanged.

## What this is not

The repository is not specifically:

- a blockchain or cryptocurrency protocol;
- a zero-knowledge system;
- a legal-evidence or discovery product, or a legal protocol;
- a smart-contract framework;
- a generic audit-log implementation;
- a category-theory library;
- a generic state-machine verification project; or
- an alternate-reality game or deliberately theatrical verification artifact.

It is not a relabeling of ordinary proof theory or programming-languages
metatheory, and it is not a claim that all institutional processes reduce to
one calculus. All source and verification commands are public; campaign
records are provenance and scope control, not a withheld or interactive
reveal.

Any of those areas could supply an application or model, but none is the
subject that defines the project. “Receipt” names the rule-specific semantic
evidence type, not a transaction receipt; “custody” is a family-specific
provenance-intactness relation, not necessarily evidentiary chain-of-custody;
and “Atlas” names a collection of bounded mappings, not a categorical
equivalence.

## Applications boundary

### The formal subject

The formal subject is governed admissibility of consequential judgments and
transitions: which evidence and resources justify them, which refusals block
them, and which origin-, history-, custody-, spend-, or obligation-sensitive
facts survive.

### Possible instantiations

Depending on the calculus and instance, the structures may be used to model
operational automation, deployment and promotion, administrative workflows,
incident response, security authority boundaries, evidence-bearing inquiry,
resource-consuming transitions, or distributed and institutional decision
systems. This is an applications boundary, not a declaration that any named
production system already implements the formal surface.

### Non-exclusive examples

Blockchain systems, legal evidence processes, hardware enclaves, and
cryptographic protocols may instantiate parts of the theory. None is the
defining application domain, and no property distinctive to those domains is
inherited without a separate formal model and theorem.

## A bridge to standard terminology

The [semantic guardrail table in the public README](../README.md#semantic-guardrails)
gives the complete entry map. Its central rule is that familiar terminology is
an analogy unless a named type or theorem makes it exact. `Witness`, `Refusal`,
`Standing`, `Custody`, `Authority`, `Spend`, and `Obligation` remain distinct;
“proof object,” “capability,” “effect,” “trace,” and “certificate” do not
replace them wholesale. For readers who know the neighboring literatures —
linear logic, deontic logic, CSP refusals, break-glass access control,
provenance, object capabilities — [`RELATED-WORK.md`](RELATED-WORK.md) names
each nearest structure and states the delta explicitly.

## Why “hostile countermodel” is a technical term

The adjective means that the model is constructed adversarially against a
proposed semantic lift. It preserves plausible neighboring premises—and often
the tempting target fact—while changing or withholding the one load-bearing
receipt or condition. Surviving those premises while breaking the unjustified
conclusion is its qualification role.

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
to “valid state transition.” It is not an exceptional axiom. It is a
constructed `GovernedFamily`, relative to consumer-supplied atoms—origin,
state, actor, and step—with explicit permit, attempt, commit, receipt,
obligation, and settlement objects.

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

V16 is the current release, version `16.0.0`, released 2026-07-28. Its Zenodo
version DOI is minted by the GitHub release creation and recorded from
Zenodo's response, so it is not stated here in advance.

## Where to go next

- [`../README.md`](../README.md) — build commands, release state, and reading
  paths by audience.
- [`../WHAT-THIS-PROVES.md`](../WHAT-THIS-PROVES.md) — technical,
  claim-by-claim scope.
- [`V16-RELEASE-OVERVIEW.md`](V16-RELEASE-OVERVIEW.md) — current release scope
  and fences.
- [`V16-PUBLIC-INDEX.md`](V16-PUBLIC-INDEX.md) — exact V16 module map and
  prior-art anchors.
- [`V15-PUBLIC-INDEX.md`](V15-PUBLIC-INDEX.md) — exact V15 module and adapter
  map.
- [`V15-PUBLIC-HOSTILE-AUDIT_2026-07-22.md`](V15-PUBLIC-HOSTILE-AUDIT_2026-07-22.md)
  — representative collapse ledger and formal pins.
- [`calculus/README.md`](calculus/README.md) — v14 conceptual, mathematical,
  and Lean-reference entrances.
- [`../CLAIM-REGISTER.md`](../CLAIM-REGISTER.md) — audited SOUND / BROKEN /
  STALE / OPEN claims.
