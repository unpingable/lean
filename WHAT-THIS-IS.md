# What this is

This is a Lean 4 proof workbench for small, auditable kernels about
admissibility.

The common question is not "can this system act?" but:

> when does what has been presented actually license what follows?

Most authorization systems ask whether a caller has the right role, token, or
permission. These proofs are about a different failure surface: cases where
evidence, standing, freshness, authority, or transition get mistaken for more
than they can support.

The payload is not the authority. A system that cannot tell an assertion of
authority from the real thing will eventually launder one into the other: stale
credentials read as fresh, a dead surface read as healthy, a guess promoted to a
verdict, a proxy mistaken for the thing it replaced.

Most modules follow the same pattern:

1. name the boundary;
2. model the thing being offered as support;
3. model the thing it is being used to justify;
4. prove that the unsupported move cannot cross the boundary.

Some modules audit claims from the Δt research series. Others form the
original Admissibility Kernels 1.0 surface: authority, standing, freshness,
surface authorization, witness invariance, state transition, execution, and
corrective layers. That earlier surface is a set of small kernels, not by
itself the v14 calculus.

v14 separately assembles the capital-C **Admissibility Calculus**: an indexed
governed-family contract with native witnesses and refusals, separate
standing/custody/obligation books, exact refusal-packet encodings, comparison
receipts, stored-decision crossings, and an origin/history-bound BreakGlass
instance. It remains bounded and explicit rather than a universal theory of
institutions.

The point is not to prove an entire institution, platform, incident, or
distributed system correct. The point is smaller and more useful: make category
errors mechanically visible before they become architecture.

Lean alone does not prove that a runtime implements any of this. A runtime
claiming correspondence must name its exact scope, supply an exact map,
executable preservation and transport evidence, and revision-bound
qualification receipts showing that every required distinction survives. A
formal refinement proof does not waive those artifacts.

This is a proof workbench, not an oracle.
