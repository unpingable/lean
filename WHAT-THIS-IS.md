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
admissibility kernel itself: authority, standing, freshness, surface
authorization, witness invariance, state transition, execution, and corrective
layers.

The point is not to prove an entire institution, platform, incident, or
distributed system correct. The point is smaller and more useful: make category
errors mechanically visible before they become architecture.

This is a proof workbench, not an oracle.
