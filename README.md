# Lean Proofs

Formal verification of structural claims from the [Δt framework](https://github.com/unpingable/papers) paper series and related working papers.

## What's here

### Paper-anchored modules

**`LeanProofs/TaxonomyGraph.lean`** — Formal encoding of the cybernetic failure taxonomy (15 domains, 14 primitive + 1 composite). Encodes the pipeline graph, role classifications, and reinforcing loops as separate relations. Proves reachability, terminality, role distinctness, and decomposition claims. Cashes out into Paper 15 (sharpen + expose looseness), with secondary tie-ins to P16 and P22.

**`LeanProofs/BranchSelector.lean`** — Dual-budget closure-family selection. Budget asymmetry / priming / susceptibility. Cashes out into Paper 9 (certify + sharpen).

**`LeanProofs/PersistenceModel.lean`** — Five-state Δc→Δh dynamics. Cumulative rollback depletion under detached commits; three-way recovery distinction. Cashes out into Paper 18 (sharpen + bridge; Appendix A v1.1 candidate).

**`LeanProofs/OpsMasking.lean`** — Operational masking, case (i) projection clause. Pointwise-equal projected actions produce identical trajectories. Cashes out into Paper 23 (bridge + certify).

**`LeanProofs/Paper24SharedVision.lean`** — Algebraic shard for Paper 24's §4 metric probes. Sign correction on Proposition 2.

### Infrastructure substrate (no paper anchor)

**`LeanProofs/Admissibility/`** — Governor-neutral authority kernel. Four modules: `Authority.lean` (verdict algebra), `StateTransition.lean` (partitioned governance state + `StepAllowed`), `Derivation.lean` (read-side bridge), `Execution.lean` (`AuthorizedStep` requires both mutation standing and claim verdict). Warrants: *governance-state mutation requires both mutation standing and an authorized claim verdict, and a revoked basis cannot produce an executable authorized step.* See [`LeanProofs/Admissibility/README.md`](LeanProofs/Admissibility/README.md) for the four-module breakdown. Substrate for future Governor (`agent_gov`) implementation citation; not paper-claim cashout.

**`LeanProofs/RepairOperator.lean`** — Sovereign repair operator. No paper anchor; formalizes the working note `working/sovereign-repair-operator.md`.

### Skeleton (deferred)

**`LeanProofs/Admissibility.lean`** — P27 obligation skeleton (namespace `P27`). Has `sorry`s; intentionally **not** wired into `LeanProofs.lean` root. Sibling but independent from the four `Admissibility/*` kernel modules above.

### First result

**(2026-04-02):** The informal claim "Δh is the universal sink" is false as a pipeline reachability claim. Δs and Δk cannot reach Δh through pipeline edges. The "universal sink" property is a dynamic/temporal attractor claim, not a graph-topological one. The prose was compressing two different kinds of claims into one sentence. See `NOTES.md` for details.

## Building

Requires [elan](https://github.com/leanprover/elan) and Lean 4.

```bash
lake build
```

## Relation to the paper series

The taxonomy is documented in `working/cybernetic-failure-taxonomy/` in the papers repo. This repo formalizes the structural claims; the papers repo holds the prose, spikes, and role map. The Lean encoding is not a replacement for the informal taxonomy — it's an ambiguity detector that forces the prose to say what it means.

For the module → paper crosswalk (which Lean modules cash out into which preprints, and whether the mapping is paper-ready), see [`PAPER-MAP.md`](PAPER-MAP.md). The paper-indexed inverse lives in the papers repo at `docs/formalization-index.md`. Claim-level audit with specific prose-location status (BROKEN / STALE / SOUND / OPEN) is in [`CLAIM-REGISTER.md`](CLAIM-REGISTER.md).

## Status

Sketch. All current proofs compile and verify. See `NOTES.md` for open questions and next steps.

## Reading the proofs

This repository is the canonical formal source. Required CI verifies that the formalization builds (`lean-action` on push); proof correctness rests on the Lean source itself, not on any rendered artifact.

The human-readable entry point for proof readers is this README plus three companion documents:

- [`PAPER-MAP.md`](PAPER-MAP.md) — module → paper crosswalk
- [`CLAIM-REGISTER.md`](CLAIM-REGISTER.md) — claim-level audit (BROKEN / STALE / SOUND / OPEN per specific prose location)
- [`WHAT-THE-LEAN-STACK-PROVES.md`](WHAT-THE-LEAN-STACK-PROVES.md) — module-level exposition of what each proof establishes and what it rules out

The papers-side companion at `docs/formalization-index.md` in the [papers repo](https://github.com/unpingable/papers) inverts the view (paper → module).

GitHub Pages renders this README at <https://unpingable.github.io/lean/> via classic Pages, so the proof reader's portal is reachable from the web without additional infrastructure. Generated `doc-gen4` API HTML is not currently published; if added later it will sit as a secondary reference layer beneath the human-readable portal, not as the front door. Proof CI proves the formalization; publication of any rendered API docs would belong to a separate non-required workflow.
