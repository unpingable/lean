# The Governed Admissibility Calculus

## When may a representation speak for reality?

Two screens can display the same green word and deserve different trust. One
screen reports a fresh observation from a live evidence pipeline. The other is
served by a healthy HTTP process whose observer stopped updating durable state
hours ago. The visible answer is the same. The evidence supporting its use is
not.

The Governed Admissibility Calculus studies this gap between a representation
and the evidence that entitles it to support a particular judgment. Here,
*admissibility* is always relative to a complete claim and a native evidence
system. It is not a universal label attached to an endpoint, record, or Boolean.

The calculus asks:

> What information must remain attached to a decision so that later summaries,
> translations, and combinations do not claim more than the original evidence
> established?

Its answer has three parts. Keep the complete claim rather than only its visible
endpoint. Return positive or negative evidence indexed by that claim. Require
every later representation to state and prove the exact relation it preserves.

The monitoring story is an analogy, not a modeled runtime. The public Lean
development supplies small formal instances—evidence-age licensing
(`Weathering`), bounded reachability, and exceptional authority (`BreakGlass`)
—that isolate the same representational failures.

## One example, four kinds of information

Imagine a worker, an observer, and a health endpoint. The observer periodically
writes a durable sample. At noon, all three components work. At 12:05, the
observer loses access to storage. At 14:00, the worker and endpoint process are
still alive, and the endpoint can still read the noon sample.

The question “is the service healthy?” is too coarse. A useful judgment needs
at least the sample condition and the intended use. An old sample may be
unacceptable for automatic failover but useful for a historical display.

The calculus gives names to the relevant pieces:

- A **claim** is the full question being decided. It may include origin,
  history, phase, and intended use—not merely the displayed endpoint.
- A **witness** is positive data for one exact claim.
- A **refusal** is structured negative data for one exact claim. It is stronger
  than failure to find a witness.
- **Standing** records the basis required to make the claim.
- **Custody** records the provenance condition that a witness must preserve.
- **Obligation** records an outstanding duty. The core calculus does not say
  how duties open or close.

These are project terms, but the distinction is ordinary. The noon sample may
still be real while lacking standing for a claim about 14:00. Its provenance
may remain intact while it is too old for direct reliance. A duty to reprobe
may exist without proving the service healthy or unhealthy.

Evidence-age licensing, formally named **Weathering**, captures this pattern.
It distinguishes direct reliance from downgrade, reprobe, and explicit stale
carry. Fresh evidence may support direct reliance. Stale evidence cannot
testify directly, but it can still be downgraded or carried as stale. The
underlying proposition has not been declared false; the licensed use has
changed.

> **Boundary note.** Weathering is one concrete instance. The core calculus
> does not impose clocks, evidence ages, or these four dispositions on every
> governed family.

**Lean anchor.**
[`Weathering.Native`](../../LeanProofs/Admissibility/Calculus/Instances/Weathering/Native.lean)
defines the evidence states, dispositions, and native licensing judgment.
[`Weathering.lean`](../../LeanProofs/Admissibility/Calculus/Instances/Weathering.lean)
packages that judgment as a governed family.

## Claims are larger than answers

A convenient output type often hides the real claim. A health endpoint returns
a Boolean, so “health” becomes a Boolean. A workflow reaches state `s`, so
reachability becomes a property of `s`. A permit contains a status field, so
authority becomes a property of that field. In each case, the output may have
erased the coordinate that distinguishes a supported claim from an unsupported
one.

The bounded-reachability example makes the problem exact. Two claims point to
the same final state, `claimed`:

```text
funded origin ── lawful recorded step ──▶ claimed
bare origin   ── forward-closed barrier ─╳ claimed
```

The funded claim has a replayable run. The bare claim has a **Barrier**: a
region containing the bare origin, closed under every lawful step, and
excluding the goal. The Barrier is a negative certificate, not a search
timeout.

If a checker receives only the endpoint, it receives the same value for both
claims. Faithfulness would require it to answer true for the funded claim and
false for the bare one. No Boolean can do both.

The generic claim-erasure theorem states precisely this conditional result. If
a projection maps one witnessed claim and one refused claim to the same value,
no Boolean checker through that projection can agree with authority on every
original claim.

> **What does not follow.** The theorem does not condemn abstraction or
> Booleans in general. It applies when an exhibited projection fiber contains
> both a witnessed and a refused claim. A narrower use may need less
> information; that narrower adequacy must be proved.

This suggests a practical interface test. For every represented value, inspect
the original claims that map to it. Are they uniform for the judgment the
consumer intends to draw? A projection can be adequate for “is the obstruction
log empty?” and inadequate for “which native refusal occurred?”

**Lean anchor.**
[`no_claim_erasing_check_is_faithful`](../../LeanProofs/Admissibility/Calculus/Core.lean)
is the generic opposed-pair theorem.
[`signature_refuses_endpoint_only_checks`](../../LeanProofs/Admissibility/Calculus/Instances/BoundedPaidReachability.lean)
is the funded/bare instance. BreakGlass supplies the analogous
[`phase_only_checker_cannot_be_faithful`](../../LeanProofs/Admissibility/Calculus/Instances/BreakGlass.lean)
for lifecycle origin.

## The common object: a governed family

Different evidence systems need not share one native semantics. They can share
a disciplined interface.

A **governed family** declares:

```text
Claim                          the complete native question
Witness claim                  positive evidence for that claim
Refusal claim                  negative evidence for that claim
Standing claim                 basis for making the claim
Custody claim                  provenance condition
Obligation claim               outstanding-duty condition
decide claim                   either a witness or a refusal
```

It also supplies three laws. A witness and refusal for the same claim cannot
coexist. Every witness entails standing. Every witness preserves custody.

The evidence types depend on the claim. This makes the index part of their
meaning. A refusal of stale direct reliance is not a refusal of downgrade. A
Barrier rooted at the bare origin is not automatically a Barrier at the funded
origin. A foreign-origin BreakGlass refusal cannot be reassigned to a native
settled claim.

The family does not prescribe a transition system, a universal refusal enum,
or an obligation lifecycle. Weathering uses a proposition-valued native
witness. Bounded reachability stores a run. BreakGlass uses phase-specific,
origin-sensitive data. Their commonality is the indexed decision shape, not a
claim that the native meanings are interchangeable.

**Lean anchor.**
[`GovernedFamily`](../../LeanProofs/Admissibility/Calculus/Core.lean) is the
ten-field public structure. The interface currently lives in `Type`, rather
than being universe-polymorphic; that is an implementation boundary, not a
mathematical impossibility result.

## Authority and the three books

The word “authorized” often compresses several questions:

- Was there a basis for making this claim?
- Does the evidence preserve provenance?
- Is some duty still open?
- Does positive evidence for this exact claim exist?

The calculus keeps these questions separate. **Authority** is defined as the
existence of a native witness for the claim. It is not a fourth field that an
instance may assert independently.

```text
witness exists ──▶ authority ──▶ standing
                         └──────▶ custody

obligation remains a separate family-native book
```

The arrows do not reverse. Standing is necessary for a witness but does not
manufacture one. Custody must be preserved by a witness but does not repair a
missing witness. An empty obligation book does not create authority.

Concrete instances make these limits observable. The bare reachability claim
has vacuous custody and no authority. A BreakGlass audit-laundering claim has
settlement standing and is refused because its retained audit history is not
clean. The bounded paid family has no obligations, yet its bare claim remains
refused.

Authority deliberately forgets witness multiplicity. Two distinct native
witness values do not become two distinguishable authority values. A consumer
that needs to count or compare evidence must retain the native witnesses.

> **Core versus instance.** The core proves that authority entails standing
> and custody. BreakGlass alone supplies its obligation lifecycle. No generic
> rule says when obligations open, persist, compose, or close.

**Lean anchor.** `GovernedFamily.Authority`,
`authority_requires_standing`, `authority_preserves_custody`,
`authority_has_no_multiplicity`, and `refusal_refutes_authority` are in
[`Core.lean`](../../LeanProofs/Admissibility/Calculus/Core.lean).

## A decision should return evidence

A Boolean tells a caller which branch won. It does not say why.

For a claim `c`, the governed decision has the shape:

```text
decide c : Witness c  OR  Refusal c
```

Every claim produces one branch. Each family supplies its own decision; the
interface does not promise a general search algorithm. A family with two
claims may decide them by two explicit cases.

The Boolean view remains useful. “The decision took the witness branch” is
equivalent to authority. But that view merges every witness into `true` and
every refusal into `false`. It cannot recover evidence identity.

The distinction matters for the green endpoint. A red or unknown status can
say that direct reliance failed. A structured refusal can say that the durable
sample was stale for the requested use. Those are different representations.
Both may be honest, but only the second retains the reason.

It also matters when decisions can change. Suppose a caller asks for a summary,
then later asks for an explanation. If the system reruns a state-sensitive
checker, the explanation may come from a different event. A later section uses
a **stored decision**—the retained native result from the original check—to
keep every projection tethered to one evidence-producing act.

**Lean anchor.** `GovernedFamily.decide` and
`authority_iff_decide_isLeft` are in
[`Core.lean`](../../LeanProofs/Admissibility/Calculus/Core.lean).

## From refusal to diagnostic spine

Different families use different refusal types. A downstream diagnostic layer
therefore needs a way to translate them without pretending they share one
native enum.

A **refusal packet** contains a claim and a refusal indexed by that claim. A
**refusal spine** is the `PathVerdict` projection of a native decision. A
witness becomes an empty obstruction log. A refusal becomes a singleton log in
a chosen diagnostic vocabulary.

This permissive projection preserves the clean/obstructed judgment even if it
maps every refusal to the same symbol. That is enough when a consumer asks only
whether some refusal occurred. It is not enough when the consumer must recover
which claim and refusal produced the obstruction.

An **exact negative-evidence projection**, formally `LosslessEncoding`, adds a
partial decoder with two requirements:

1. decoding an encoded refusal returns the complete original packet;
2. every successful decode identifies the canonical encoding of that packet.

These laws make refusal-packet encoding injective. A one-value domain cannot
satisfy them when two distinct refusal packets exist.

The positive statement is deliberately narrow:

> The encoding exactly preserves refusal packets. Accepted witness identity
> remains in the native decision and is not serialized by the verdict.

Decoding is also not historical authentication. A value can decode to a valid
packet shape without proving that a native checker returned that packet during
a real execution. That provenance comes from a stored checked result or from a
separate runtime correspondence argument.

**Lean anchor.** [`Spine.lean`](../../LeanProofs/Admissibility/Calculus/Spine.lean)
defines `RefusalPacket`, `SpineEncoding`, `LosslessEncoding`, and the exact
recovery and injectivity theorems.

## Transport: preserve judgment, recover identity only when earned

A `PathVerdict` is an ordered obstruction log. The empty log is
authority-bearing; composing verdicts appends their logs. A composite is empty
exactly when both parts are empty, so an existing obstruction cannot disappear
through composition.

Diagnostic vocabularies often need renaming. A domain map changes every native
domain obstruction while leaving shared core obstructions untouched. Every
total map preserves and reflects emptiness. It therefore preserves the
authority-bearing judgment.

Exact native identity is stronger. A noninjective map can merge two
obstruction names while preserving the fact that the log is nonempty. Backward
recovery of native domain membership requires an injective map.

```text
any total domain map     preserves clean versus obstructed
injective domain map     also supports exact backward native identity
```

A **located verdict** adds an identifier to each retained obstruction. In the
sanctioned fold, the output label is carried from the input edge that produced
the fault. Soundness traces every output pair back to such an input.

This is **carried identity**, not authenticated identity. The public type also
allows raw construction and relabeling. The theorem says that the fold
preserves supplied labels; it does not prove that an external source assigned
those labels truthfully.

**Lean anchor.**
[`PathVerdict.Core`](../../LeanProofs/Admissibility/PathVerdict/Core.lean),
[`Domains`](../../LeanProofs/Admissibility/PathVerdict/Domains.lean), and
[`Located`](../../LeanProofs/Admissibility/PathVerdict/Located.lean) define the
verdict algebra, domain transport, and construction-relative location laws.

## Comparison without forced unification

Two systems may need comparison without sharing one claim type or one native
semantics. Forcing both into a synthetic master judgment can erase the very
difference under review.

The comparison framework starts with one source judgment, one target judgment,
and one declared map between their carriers. A proof-carrying receipt then says
what that map supports:

- **Exact judgment:** the source predicate holds exactly when the target
  predicate holds after mapping.
- **Exact representation:** exact judgment plus canonical recovery of every
  source value.
- **Directional with loss:** source truth is preserved, and an explicit pair
  shows that representation identity is merged.
- **Separation:** an explicit source-positive case maps to a target-negative
  case, while a target-positive control shows that the target judgment is not
  vacuous.

Exact judgment and exact representation are intentionally different. A map can
preserve a predicate perfectly while collapsing several positive source
values. Recovery requires the stronger receipt and implies injectivity.

BreakGlass uses separation rather than pretending that exceptional and
ordinary authority are two presentations of one judgment. Exceptional
authority can coexist with a retained ordinary denial. Settlement standing can
coexist with a non-clean audit history.

> **Repository status.** The public Lean surface defines the comparison
> framework and its proof obligations. The concrete seven-entry comparison
> table is retained supporting evidence, not public Lean doctrine.

**Lean anchor.** [`Comparison.lean`](../../LeanProofs/Admissibility/Calculus/Comparison.lean)
defines the four receipt types and their principal consequences.
[`BreakGlass/Comparison.lean`](../../LeanProofs/Admissibility/Calculus/Instances/BreakGlass/Comparison.lean)
contains the two public separation receipts.

## Decide once, then cross

A **crossing** combines exactly two governed judgments while retaining each
side’s evidence. It is not a claim that the systems have been unified.

Why store the decisions? A checker may be expensive, state-sensitive, or able
to return different witness data on different runs. If a summary and its
diagnostic are computed from separate evaluations, they need not describe the
same event.

The crossing therefore evaluates each native family once and stores the two
results. Every later result, verdict, located diagnostic, and comparison view
is a pure function of that stored pair.

```text
left decide ─┐
             ├─▶ stored pair ─▶ result ─▶ verdict / location / comparison
right decide ┘
```

There are four branches:

| Left | Right | Stored crossing result |
|---|---|---|
| witness | witness | both witnesses |
| refusal | witness | left refusal and right witness |
| witness | refusal | left witness and right refusal |
| refusal | refusal | both refusals |

The mixed branches retain the successful witness. The double-refusal branch
retains both refusals in left/right order. With exact refusal spines, each
diagnostic decodes to its native packet.

Crossing authority is exactly the conjunction of the two component
authorities. One successful side cannot cure the other side’s refusal. The
core crossing adds no obligation interaction, payment rule, or lifecycle
composition.

**Lean anchor.** [`Crossing.lean`](../../LeanProofs/Admissibility/Calculus/Crossing.lean)
defines `CheckedCrossing`, its single evaluation boundary, the four-way stored
fold, and exact mixed/double-refusal recovery.

## The three recurring instances

The core calculus supplies a common form. The concrete instances supply native
meaning.

### Evidence-age licensing (`Weathering`)

Weathering pairs an evidence condition with an intended disposition. Direct
reliance requires a testimony license. Downgrade, reprobe, and explicit stale
carry remain available without it. Stale evidence can therefore be refused for
direct reliance and witnessed for downgrade.

Weathering is static. Its witness is proposition-valued and has no meaningful
multiplicity. It proves no clock model or monitor implementation.

### Bounded reachability and `Barrier`

The funded claim carries a typed run from its origin to the fixed endpoint. The
bare claim carries a forward-closed exclusion certificate (`Barrier`). Both
claims name the same endpoint, which supplies the concrete erasure
counterexample.

The word “paid” in the native module does not make this a payment-discharge
theorem. The positive run performs admission, not payment. The paid book at the
endpoint is empty, custody over it is vacuous, and the obligation book is
empty. The bounded positive claim is lawful reachability for one fixed
fixture.

### Origin- and history-sensitive exception (`BreakGlass`)

BreakGlass is a bounded instance relative to consumer-supplied atoms: origin,
state, actor, and step. Claims retain a lifecycle origin and phase. Four native
phases are witnessed. Two laundering claims—ordinary authorization and clean
audit history—are refused.

The lifecycle origin qualifies every reference. Matching local numbers under
different origins do not become the same reference. A foreign origin is
refused at every phase, so a phase-only checker is too coarse.

BreakGlass supplies its own obligation lifecycle: no obligation before commit,
one exact obligation at commit, and closure at settlement. This is an instance
result, not a core rule. The audit trail is bounded to a singleton, and state
progression requires an explicit hypothesis that the supplied step changes the
state.

Exceptional authority does not imply ordinary authorization. Settlement
standing does not imply clean audit history. The instance permits an
exceptional act without retroactively normalizing its ordinary or historical
status.

### Crossings of the instances

Weathering × bounded reachability exercises all four stored branches. A fresh
gate cannot cure a bare passage. A funded passage cannot cure stale direct
reliance. A double failure retains both exact refusals.

Weathering × BreakGlass similarly retains the native origin, refusal, and
obligation observations. Neither construction is an N-ary composition theorem
or a universal emergency calculus.

**Lean anchor.** The public instance modules live under
[`Calculus/Instances`](../../LeanProofs/Admissibility/Calculus/Instances/).
The [declaration index](declaration-index.md) maps each principal result to its
exact source.

## Read the bounded statement first

Formal vocabulary can tempt a reader into a stronger claim than the theorem
states. The safest editorial rule is to state the correct narrow result first.

- The two-claim reachability family decides lawful history exactly. It does not
  decide arbitrary reachability.
- The refusal encoding recovers exact refusal packets. It does not serialize
  accepted witness identity.
- Domain renaming preserves clean versus obstructed. Exact native obstruction
  recovery additionally requires injectivity.
- Located folds carry input labels. They do not authenticate those labels.
- BreakGlass settlement closes one designated origin-qualified obligation. The
  core has no generic obligation lifecycle.
- The public comparison framework defines valid receipt shapes. Its concrete
  comparison ledger is not public Lean doctrine.

Some missing rules are defeated by concrete counterexamples. Standing does not
imply authority because the BreakGlass audit-laundering claim has standing and
a refusal. Custody does not imply authority because the bare reachability claim
has vacuous custody and a refusal.

Other statements are outside the model rather than refuted by it. The calculus
defines no runtime-conformance predicate, authenticated-label source, universal
payment lifecycle, or general emergency process semantics. A future extension
may add such objects, but they do not follow from the present core.

## What the calculus does not supply

The calculus does not define one global `Admissible` predicate. Each family
keeps its native judgment. The shared predicate `Authority F c` always names a
family and claim.

It does not supply generic process semantics. The reachability and BreakGlass
instances define bounded native processes; the core does not absorb every
transition system in the repository.

It does not make obligation compositional. A crossing combines evidence from
two families but adds no rule for opening, transporting, or discharging their
obligations.

It does not authenticate data merely because the data are present. A decoded
packet is not an execution receipt. A carried location is not self-signing. A
source pin in a comparison record is not verified by its field alone.

It does not prove that a runtime conforms to the formal model. Such a claim
needs an exact correspondence map for every governed distinction in scope,
executable preservation and transport evidence, and revision-bound
qualification. A formal refinement proof may discharge some of those duties,
but a Lean theorem does not identify an unmodeled program with its definitions.

## Formal and repository status

The conceptual argument above can be read without repository history. For
traceability, the public implementation is rooted at
[`LeanProofs.Admissibility.Calculus`](../../LeanProofs/Admissibility/Calculus.lean).
A **stable root** is a repository compatibility surface whose exact imports are
registered; it is a publication fact, not a mathematical premise.

The root contains the governed-family core, the public verdict substrate,
refusal encoding, comparison framework, binary crossing, and the bounded
instances described above. The concrete comparison table and several hostile
or predecessor artifacts remain supporting evidence outside the public Lean
surface.

Proof and custody accounting is intentionally kept out of the main exposition:

- the [declaration index](declaration-index.md) maps the principal prose claims
  to exact Lean declarations;
- the [numbered reference chapters](README.md#lean-and-audit-reference) give a
  denser module-by-module account;
- the [claim register](../../CLAIM-REGISTER.md) records claim-level status and
  nonclaims;
- the [readiness ledger](../V14-READINESS-LEDGER.md) preserves admission
  history, exact proof footprints, and retained adverse evidence.

No part of this documentation claims runtime conformance, a new release, or a
change to the public Lean surface. The mathematical object is the compiled
calculus; this document is a reader-facing route into it.

## Representation as testimony

A representation never carries the whole world. It need only carry what its
intended judgment requires. But every compression creates a proof obligation.

A green monitor may honestly report process liveness and still lack evidence
for current operational health. Funded and bare claims may share an endpoint
while differing in lawful history. Stale evidence may support downgrade while
refusing direct testimony. Exceptional authority may permit an act while
retaining ordinary denial and a marked audit history.

The calculus makes these distinctions explicit. Preserve the claim. Return the
evidence. Name the loss. Store the decision that downstream views summarize.
Use exact recovery only where an injective or inverse law has been proved.

That is the central discipline: a representation does not acquire authority
merely by being the value a system happened to store.
