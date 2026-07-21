# 1. Motivation and scope

Suppose two records display the same endpoint: “resource present.” One record
was reached from an origin holding a warrant; the other simply began with the
same stamped resource. Endpoint equality does not make the histories equally
entitled. The public bounded-paid instance makes this example literal: both
claims target `claimed`, but `fromFunded` has a replayable witness while
`fromBare` has a forward-closed barrier
([`PaidClaim`](../../LeanProofs/Admissibility/Calculus/Instances/BoundedPaidReachability.lean#L87),
[`boundedPaidReachability`](../../LeanProofs/Admissibility/Calculus/Instances/BoundedPaidReachability.lean#L130)).

This is the calculus's central representational problem. A projection may retain
the visible answer while erasing the claim distinction that made the answer
auditable. The generic theorem
[`no_claim_erasing_check_is_faithful`](../../LeanProofs/Admissibility/Calculus/Core.lean#L159)
shows that if a projection identifies one witnessed claim with one refused
claim, no Boolean checker through that projection can agree with authority on
all claims. The bounded-paid theorem
[`signature_refuses_endpoint_only_checks`](../../LeanProofs/Admissibility/Calculus/Instances/BoundedPaidReachability.lean#L190)
instantiates the result at the shared endpoint.

> **Theorem — `GovernedFamily.no_claim_erasing_check_is_faithful`.**  If
> `proj c₁ = proj c₂`, `c₁` has a witness, and `c₂` has a refusal, then there is
> no `check : E → Bool` that is true exactly when every original claim has
> authority. Its significance is conditional and exact: it condemns a
> projection that collapses this opposed pair, not abstraction in general.

## What the public calculus contains

The exact stable root imports:

- the governed-family core;
- static Weathering and bounded paid-reachability instances;
- the refusal-packet spine and lossless adapters;
- the indexed comparison *framework*;
- a binary stored-decision crossing and its Weathering/paid inhabitant;
- an origin/history-bound BreakGlass family, spine, two comparison
  separations, and Weathering/BreakGlass crossing.

The import list is the authoritative list
([`Calculus.lean`](../../LeanProofs/Admissibility/Calculus.lean#L37)). Its
transitive dependencies include the `PathVerdict` core, edges, domain transport,
and located diagnostics. The [v14 readiness ledger](../V14-READINESS-LEDGER.md)
records the seven admission rungs and the material deliberately retained in
skunkworks custody.

## What “calculus” means here

It means this exact custody-closed object under namespace
`Admissibility.Calculus`; it does not mean a universal logic of all repository
kernels. The older `Admissibility.Kernels` compatibility root explicitly
remains eight separate kernels and is not retroactively widened
([`AdmissibilityKernels.lean`](../../LeanProofs/Admissibility/AdmissibilityKernels.lean#L5)).

There is no repository-wide declaration named global `Admissible` that combines
Weathering, reachability, BreakGlass, process execution, and every other kernel.
Weathering's native `Admissible` is local to that instance
([source](../../LeanProofs/Admissibility/Calculus/Instances/Weathering/Native.lean#L74)).
The shared abstraction is `GovernedFamily`, not a shared native semantics.

## The boundary of entitlement

The abstract answer has six pieces:

1. a claim retains every distinction needed by its native decision;
2. witness and refusal are data indexed by that claim;
3. standing, custody, and obligation remain distinct predicates;
4. authority is *derived* as existence of native witness data;
5. `decide` is total and returns a witness or a refusal;
6. exported transports and crossings preserve the diagnostic artifacts rather
   than silently rerunning or flattening them.

This is a contract for mathematical representations. It is not, without a
separate correspondence proof and executable evidence, a statement about which
software process actually ran or who possessed runtime authority.
