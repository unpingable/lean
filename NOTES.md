# Taxonomy Lean Sketch: Status Notes

**Date:** 2026-04-02
**Status:** First compilation successful. All proofs verified (490ms).

## What's proven

- Terminal nodes (Δg, Δa) have no outgoing pipeline edges
- Δx and Δh have no outgoing pipeline edges
- Pipeline reachability from Δn, Δo, Δw, Δp, Δe, Δr, Δb, Δc to Δh
- Framing cascade (Δn → Δb → Δc → Δh) has distinct role at each step
- Roots have outgoing edges; junction (Δb) has both incoming and outgoing
- Δi decomposes into Δn + Δr + Δw by definition

## Negative result (the real finding)

- **Δs and Δk do NOT reach Δh through pipeline edges**
- Δs → Δm → Δg/Δa (terminal dead ends)
- Δk → Δx (no outgoing edges)
- Therefore: **"Δh is the universal sink" is FALSE as a pipeline reachability claim**
- The informal prose was compressing two different claims into one sentence

## Open questions

- **Static pipeline vs dynamic attractor:** Δh may still be a dynamic attractor under persistence, but that's a temporal claim the static graph can't represent. Needs a separate relation if formalized.
- **Δx as dead end:** Classified as cross-scale transmission / amplifier, but has no outgoing pipeline edges. Amplifies in-place — is that a different kind of edge, or does the role need reclassifying?
- **Therapeutic inversion count:** 13/15 in the Lean encoding vs 11/14 in the role map. Discrepancy is definitional strictness, not a bug.

## Next steps (not tonight)

1. Compute full transitive closure / reachability matrix (replace artisanal proofs)
2. Formalize claim partition in prose: structural / definitional / dynamic / normative
3. Introduce dynamic relation stub if the attractor claim needs teeth
4. Do NOT add edges to rescue the universal-sink slogan
