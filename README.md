# Lean Proofs

Formal verification of structural claims from the [Δt framework](https://github.com/unpingable/papers) paper series and related working papers.

## What's here

**`LeanProofs/TaxonomyGraph.lean`** — Formal encoding of the cybernetic failure taxonomy (15 domains, 14 primitive + 1 composite). Encodes the pipeline graph, role classifications, and reinforcing loops as separate relations. Proves reachability, terminality, role distinctness, and decomposition claims.

**First result (2026-04-02):** The informal claim "Δh is the universal sink" is false as a pipeline reachability claim. Δs and Δk cannot reach Δh through pipeline edges. The "universal sink" property is a dynamic/temporal attractor claim, not a graph-topological one. The prose was compressing two different kinds of claims into one sentence. See `NOTES.md` for details.

## Building

Requires [elan](https://github.com/leanprover/elan) and Lean 4.

```bash
lake build
```

## Relation to the paper series

The taxonomy is documented in `working/cybernetic-failure-taxonomy/` in the papers repo. This repo formalizes the structural claims; the papers repo holds the prose, spikes, and role map. The Lean encoding is not a replacement for the informal taxonomy — it's an ambiguity detector that forces the prose to say what it means.

## Status

Sketch. All current proofs compile and verify. See `NOTES.md` for open questions and next steps.
