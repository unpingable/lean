# 7. Concrete instances

The common signature does not erase native substrate differences. Each instance
chooses its own claim, witness, refusal, books, and total decision.

The examples reuse three problems from the conceptual exposition: stale
evidence and requested use; funded and bare histories with one endpoint; and
exceptional authority that retains ordinary denial and audit history. Nothing
in this chapter is automatically true of every governed family.

## Weathering: static licensing

Evidence can become too old to support direct reliance while remaining useful
for downgrade or reprobe. The **Weathering** instance formalizes this licensing
distinction with five evidence states and four downstream dispositions
([native types](../../LeanProofs/Admissibility/Calculus/Instances/Weathering/Native.lean#L45)).
Direct reliance requires `canTestify = true`; downgrade, reprobe, and explicit
stale carrying remain available without that license. Its native judgment is:

```lean
inductive Admissible : Weather → Disposition → Prop
  | rely : w.canTestify = true → Admissible w .relyDirectly
  | downgrade : Admissible w .downgrade
  | reprobe : Admissible w .reprobe
  | carry : Admissible w .carryStale
```

The governed claim is `Weather × Disposition`. Witness and refusal are lifted
propositions; standing constrains only direct reliance; custody is `True`; and
obligation is `False`
([`weathering`](../../LeanProofs/Admissibility/Calculus/Instances/Weathering.lean#L48)).
The no-distortion theorem
[`weathering_authority_iff_native`](../../LeanProofs/Admissibility/Calculus/Instances/Weathering.lean#L80)
identifies family authority with the native judgment.

Weathering is static and its witness is subsingleton. The interface does not
invent history or multiplicity that the native judgment lacks. Its exact spine
uses the three-constructor `WeatherObstruction` vocabulary, with the
non-refusal `missingWitness` value deliberately decoding to `none`
([obstructions](../../LeanProofs/Admissibility/Calculus/Instances/Weathering/Obstructions.lean#L31),
[decoder](../../LeanProofs/Admissibility/Calculus/Instances/Weathering/Spine.lean#L66)).

## Bounded paid reachability: replay and exclusion

The paid substrate has proof-relevant `Run` data over staged state transitions
([`Run`](../../LeanProofs/Admissibility/Calculus/Instances/BoundedPaidReachability/Native.lean#L56)).
The public instance fixes two origins, one endpoint, one warrant, and one
positive admission run. `PaidClaim` has exactly `fromFunded` and `fromBare`.

Failure to find a run would be too weak to justify refusal. This instance uses
a forward-closed exclusion certificate, formally `Barrier origin`:

```lean
structure Barrier (origin : State Nat) where
  region : State Nat → Prop
  contains : region origin
  closed : ∀ {s a s'}, region s → Step Nat s a s' → region s'
  excludes : ¬ region claimed
```

([source](../../LeanProofs/Admissibility/Calculus/Instances/BoundedPaidReachability.lean#L101)).
[`Barrier.stays`](../../LeanProofs/Admissibility/Calculus/Instances/BoundedPaidReachability.lean#L108)
extends closure from one step to a whole run, so a witness reaching `claimed`
contradicts a barrier excluding it.

The family witness stores both an action list and its typed run. Standing and
custody are occurrence-provenance conditions over different endpoint books;
obligation is empty. The checker is a fixed two-case decision, not reachability
search. The central positive theorem is
[`authority_iff_lawful_history`](../../LeanProofs/Admissibility/Calculus/Instances/BoundedPaidReachability.lean#L157).
The negative fixture demonstrates that equal endpoints cannot replace indexed
claims.

The word “paid” must not be allowed to strengthen the theorem. The positive run
contains one `.admit`, no `.pay`; `claimed.paid` is empty, making custody
vacuous; and the obligation book is `False`. The public crossing repeats these
disclosures in
[`bounded_paid_component_custody_is_vacuous`](../../LeanProofs/Admissibility/Calculus/Instances/WeatheringBoundedPaidCrossing.lean#L164)
and
[`weathering_paid_component_obligation_books_are_empty`](../../LeanProofs/Admissibility/Calculus/Instances/WeatheringBoundedPaidCrossing.lean#L172).

## Weathering × paid reachability

The four fixtures cover fresh/stale gate × funded/bare passage
([source](../../LeanProofs/Admissibility/Calculus/Instances/WeatheringBoundedPaidCrossing.lean#L68)).
Their exact checker equations prove all four stored branches. In particular:

- a fresh gate cannot cure the bare passage
  ([`green_gate_cannot_cure_unfunded_passage`](../../LeanProofs/Admissibility/Calculus/Instances/WeatheringBoundedPaidCrossing.lean#L128));
- a funded passage cannot cure the stale direct-reliance gate
  ([`funded_passage_cannot_cure_stale_gate`](../../LeanProofs/Admissibility/Calculus/Instances/WeatheringBoundedPaidCrossing.lean#L138));
- a double failure retains and decodes both faults without shadowing
  ([`stale_bare_double_fault_nonshadowing`](../../LeanProofs/Admissibility/Calculus/Instances/WeatheringBoundedPaidCrossing.lean#L204)).

This is a binary conjunction of these declared judgments, not a payment or
settlement composition theorem.

## Bounded BreakGlass: origin and history

An exceptional act must not silently become ordinary authorization or clean
history. **BreakGlass** is a bounded instance of that separation. It is closed
only relative to consumer-supplied `Atoms`—origin, state, actor, and step. A
`LifecycleOrigin` contains authority domain, epoch, and nonce. Every reference
is indexed by a book kind and carries that origin
([source](../../LeanProofs/Admissibility/Calculus/Instances/BreakGlass/LifecycleOrigin.lean#L41)).
Consequently, equal local numbers at different origins remain unequal
([`Ref.same_local_ne_of_origin_ne`](../../LeanProofs/Admissibility/Calculus/Instances/BreakGlass/LifecycleOrigin.lean#L89)).

The governed claim is `(origin, phase)`, where four phases are witnessed and
two are laundering claims
([source](../../LeanProofs/Admissibility/Calculus/Instances/BreakGlass.lean#L51)).
Witness shapes differ by phase. A settled witness contains an origin match, a
native commit, and the native `Reconciles` relation over the full ledger.
Refusals distinguish:

- foreign origin, at every phase;
- false ordinary authorization;
- false audit cleanliness.

The total checker first compares origin, then decides by phase
([`governedFamily`](../../LeanProofs/Admissibility/Calculus/Instances/BreakGlass.lean#L210)).
[`authority_retains_claim_origin`](../../LeanProofs/Admissibility/Calculus/Instances/BreakGlass.lean#L410)
and
[`phase_only_checker_cannot_be_faithful`](../../LeanProofs/Admissibility/Calculus/Instances/BreakGlass.lean#L427)
make origin load-bearing through authority and checking.

The obligation lifecycle is exact but bounded: no obligation before commit,
one exact live obligation at commit, and closure at settlement. The audit trail
is a singleton, so no multi-entry reordering theorem follows. State change at
commit is proved only under an explicit inequality hypothesis
([`same_origin_state_progression`](../../LeanProofs/Admissibility/Calculus/Instances/BreakGlass.lean#L333)).

Two public separation receipts establish that exceptional authority does not
turn the retained ordinary verdict into `.authorized`, and settlement standing
does not clean the audit history
([comparison module](../../LeanProofs/Admissibility/Calculus/Instances/BreakGlass/Comparison.lean#L48)).
The first is deliberately verdict-level. The public module neither constructs
nor rejects the stronger native `AuthorizedStep` relation
([boundary comment and theorem](../../LeanProofs/Admissibility/Calculus/Instances/BreakGlass/Comparison.lean#L79)).

The Weathering/BreakGlass crossing stores one fresh Weathering result
and one BreakGlass result. It proves clean crossing for the four native phases,
exact structured refusal for both laundering phases and foreign origins, exact
location/decoding, and preservation of the origin and obligation observations
([crossing module](../../LeanProofs/Admissibility/Calculus/Instances/BreakGlass/Crossing.lean#L52)).
It is not an unbounded or universal BreakGlass calculus.

> **Core/instance boundary.** Weathering supplies use-sensitive static
> licensing. Bounded paid reachability supplies replay and `Barrier` evidence.
> BreakGlass supplies an origin-qualified obligation lifecycle. The core
> calculus imposes none of those native semantics.
