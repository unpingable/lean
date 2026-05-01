# Lean Proofs

This repository is a formal audit harness for the [Δt framework](https://github.com/unpingable/papers): a research series on systemic failure, temporal mismatch, authority collapse, and recovery under degraded conditions.

The prose papers make claims about how complex systems degrade, recover, misread themselves, or substitute proxies for reality. This repo translates selected claims into Lean so they can be checked against explicit definitions instead of persuasive prose.

Some claims survive. Some narrow. Some break.

That is the point.

Lean is used here as a pressure chamber for theory: it helps distinguish structural claims from slogans that were useful for discovery but too loose to carry formal weight. Failed claims are kept as evidence of where the original prose overreached — see [`CLAIM-REGISTER.md`](CLAIM-REGISTER.md) for the BROKEN / STALE / SOUND / OPEN audit.

## Why Lean

The Δt framework began as prose theory. Prose is good at discovery, but it can hide assumptions, collapse distinct cases, or make causal claims that are only directionally true.

Lean forces selected claims to be stated as definitions and theorem statements. When a claim fails, the failure is treated as evidence: the theorem was overstated, the definitions were wrong, or the prose was relying on an unstated assumption. The repo's value is less the surviving theorems than the disciplined damage report on the rest.

This repo does not claim that Lean proves the whole theory true. It does not replace case studies, simulations, or operational evidence. It is a forcing function against theory-by-metaphor.

## Companion repos

- **Papers repo:** [`unpingable/papers`](https://github.com/unpingable/papers) — prose papers, working notes, primitives, and the research-program structure. The paper-side crosswalk at [`docs/formalization-index.md`](https://github.com/unpingable/papers/blob/main/docs/formalization-index.md) inverts this repo's view (paper → module).
- **This repo (Lean):** formal claim register, proof attempts, corrected theorem statements, and the BROKEN / STALE / SOUND audit. Module → paper crosswalk lives in [`PAPER-MAP.md`](PAPER-MAP.md).

## What's here

### Paper-anchored modules

**`LeanProofs/TaxonomyGraph.lean`** — Formal encoding of the cybernetic failure taxonomy (15 domains, 14 primitive + 1 composite). Encodes the pipeline graph, role classifications, and reinforcing loops as separate relations. Proves reachability, terminality, role distinctness, and decomposition claims. Cashes out into Paper 15 (sharpen + expose looseness), with secondary tie-ins to P16 and P22.

**`LeanProofs/BranchSelector.lean`** — Dual-budget closure-family selection. Budget asymmetry / priming / susceptibility. Cashes out into Paper 9 (certify + sharpen).

**`LeanProofs/PersistenceModel.lean`** — Five-state Δc→Δh dynamics. Cumulative rollback depletion under detached commits; three-way recovery distinction. Cashes out into Paper 18 (sharpen + bridge; Appendix A v1.1 candidate).

**`LeanProofs/OpsMasking.lean`** — Operational masking, case (i) projection clause. Pointwise-equal projected actions produce identical trajectories. Cashes out into Paper 23 (bridge + certify).

**`LeanProofs/Paper24SharedVision.lean`** — Algebraic shard for Paper 24's §4 metric probes. Sign correction on Proposition 2.

### Infrastructure substrate (no paper anchor)

**`LeanProofs/Admissibility/`** — Governor-neutral authority kernel. Five modules: `Authority.lean` (verdict algebra), `StateTransition.lean` (partitioned governance state + `StepAllowed`), `Derivation.lean` (read-side bridge), `Execution.lean` (`AuthorizedStep` requires both mutation standing and claim verdict), `Corrective.lean` (corrective monotonicity layer — classify-based enforcement surface, `RecoveryEnv` gate). Warrants: *governance-state mutation requires both mutation standing and an authorized claim verdict, a revoked basis cannot produce an executable authorized step, and corrective recovery cannot increase the authorized action set.* See [`LeanProofs/Admissibility/README.md`](LeanProofs/Admissibility/README.md) for the five-module breakdown. Substrate for future Governor (`agent_gov`) implementation citation; not paper-claim cashout.

**`LeanProofs/RepairOperator.lean`** — Sovereign repair operator. No paper anchor; formalizes the working note `working/sovereign-repair-operator.md`.

### Skeleton (deferred)

**`LeanProofs/Admissibility.lean`** — P27 obligation skeleton (namespace `P27`). Sorry-free as of 2026-05-01 (three real proofs against the local `admissible` definition; two `True`-placeholder discharges with deferred-real-statement docstrings pending substrate-accusation / causal-binding predicates). Intentionally **not** wired into `LeanProofs.lean` root — sorry-elimination does not imply wiring. Sibling but independent from the five `Admissibility/*` kernel modules above.

### First result

**(2026-04-02):** The informal claim "Δh is the universal sink" is false as a pipeline reachability claim. Δs and Δk cannot reach Δh through pipeline edges. The "universal sink" property is a dynamic/temporal attractor claim, not a graph-topological one. The prose was compressing two different kinds of claims into one sentence. See `NOTES.md` for details.

## Building

Requires [elan](https://github.com/leanprover/elan) and Lean 4.

```bash
lake build
```

## Cross-references

- [`PAPER-MAP.md`](PAPER-MAP.md) — module → paper crosswalk (which Lean modules cash out into which preprints, and whether the mapping is paper-ready)
- [`CLAIM-REGISTER.md`](CLAIM-REGISTER.md) — claim-level audit with specific prose-location status (BROKEN / STALE / SOUND / OPEN)
- [`WHAT-THE-LEAN-STACK-PROVES.md`](WHAT-THE-LEAN-STACK-PROVES.md) — module-level exposition of what each proof establishes and what it rules out
- Papers repo: [`docs/formalization-index.md`](https://github.com/unpingable/papers/blob/main/docs/formalization-index.md) — paper → module inverse view

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
