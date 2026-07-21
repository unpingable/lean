# 2. The governed family

The smallest common object is a ten-field structure
([`GovernedFamily`](../../LeanProofs/Admissibility/Calculus/Core.lean#L77)):

```lean
structure GovernedFamily where
  Claim : Type
  Witness : Claim → Type
  Refusal : Claim → Type
  Standing : Claim → Prop
  Custody : Claim → Prop
  Obligation : Claim → Prop
  exclusive : ∀ {c}, Witness c → Refusal c → False
  witness_requires_standing : ∀ {c}, Witness c → Standing c
  witness_preserves_custody : ∀ {c}, Witness c → Custody c
  decide : (c : Claim) → Sum (Witness c) (Refusal c)
```

The public signature is universe-0: these data inhabit `Type`, not an arbitrary
`Type u` ([scope fence](../../LeanProofs/Admissibility/Calculus/Core.lean#L28)).
That is an implementation boundary of the ratified interface, not a theorem
that universe polymorphism is mathematically impossible.

## Claims are the unit of judgment

`Claim` is not required to be an endpoint. It may include origin, requested
mode, phase, or other history-sensitive coordinates. Both dependent families

```lean
Witness : Claim → Type
Refusal : Claim → Type
```

can therefore have different shapes at different claims. This prevents a
generic consumer from extracting a reason and then attaching it to an unrelated
claim without constructing the dependent type.

The claim index is essential for three distinct public examples:

- Weathering claims pair a weather state with a reliance disposition
  ([instance](../../LeanProofs/Admissibility/Calculus/Instances/Weathering.lean#L48)).
- Paid claims retain the origin choice even though the endpoint is fixed
  ([`PaidClaim.origin`](../../LeanProofs/Admissibility/Calculus/Instances/BoundedPaidReachability.lean#L93)).
- BreakGlass claims retain a lifecycle origin and phase
  ([`BreakGlass.Claim`](../../LeanProofs/Admissibility/Calculus/Instances/BreakGlass.lean#L62)).

Erasing these indices loses different things: a licensing mode, provenance of
reachability, or lifecycle identity. The generic erasure theorem does not
pretend those losses are the same native phenomenon.

## Assumptions versus derived facts

The structure assumes only:

- witness/refusal incompatibility;
- witness-to-standing;
- witness-to-custody;
- a total native decision.

It assumes no generic obligation lifecycle, no conversion from a book into a
witness, and no composition operator. From those assumptions the core derives
refusal's incompatibility with authority, authority's standing and custody
consequences, checker coherence, and the claim-erasure obstruction
([core declarations](../../LeanProofs/Admissibility/Calculus/Core.lean#L103)).

## A small running example

For Weathering, a claim is `(weather, disposition)`. Direct reliance on stale
evidence has refusal data; downgrading a stale claim has witness data. The
evidence is not declared false when it becomes stale: the native theorem
[`staleness_is_not_negation`](../../LeanProofs/Admissibility/Calculus/Instances/Weathering/Native.lean#L94)
says every weather state supports some disposition. What changes is which
representation is licensed to speak directly.

This example shows why the abstraction does not prescribe one shared refusal
enum. Weathering refusal records non-testifying evidence paired with direct
reliance. Paid reachability refusal is a closed region excluding the endpoint.
BreakGlass refusal distinguishes foreign origin from two different laundering
claims. Their commonality lies in the dependent decision shape, not in the
native meanings of refusal.
