# Lean Proofs

*New here? See [unpingable.github.io](https://unpingable.github.io/) for the project root — author (James Beck), scope, and the full preprint list. This repo holds the admissibility kernel modules and serves as the formal audit harness for the Δt research series; the [papers repo](https://github.com/unpingable/papers) is the prose home. See also the [methodology page](https://github.com/unpingable/papers/blob/main/docs/methodology.md) for what the BROKEN / STALE / SOUND register is doing and why.*

## Reading the Lean repo

**This is not a process calculus. It is an admissibility kernel.**

This repository contains small Lean 4 kernels for reasoning about when evidence, standing, freshness, authorization, and transition are sufficient to support a claim or action.

The modules are intentionally narrow. They formalize recurring boundary failures: stale authority, self-certification, collapsed public surfaces, unauthorized transition, exposure without standing, and cross-boundary cascade.

A separate stack of modules audits prose claims from the Δt research series. That audit harness shares the same Lean discipline, but it is one consumer of the admissibility kernel, not the whole repo.

The public handle:

> small, auditable kernels for recurring admissibility failures.

Most modules follow the same pattern:

1. define a small model of a failure surface;
2. state the invalid inference the system must not allow;
3. prove that the inference cannot be derived under the model;
4. leave implementation, policy, and consequence outside the theorem.

The point is not to prove an entire software system correct. The point is to make category errors mechanically visible before they become architecture.

## Map

- **Admissibility kernel** — authority, standing, verdicts, state transition, execution, corrective layers.
- **Surface / receipt / witness kernels** — collapsed surfaces, public receipt refinement, witness invariance.
- **Admissibility axes** — artifact kind, numerical kind, closure, recovery margin, freshness.
- **Cross-boundary artifact specimens** — exposure, degradation, failure minting, cascade.

For the full module-by-module reference, see [`LeanProofs/Admissibility/README.md`](LeanProofs/Admissibility/README.md).

For what the current Lean stack proves, see [`WHAT-THE-LEAN-STACK-PROVES.md`](WHAT-THE-LEAN-STACK-PROVES.md).

## Calculus 1.0

**Admissibility Calculus 1.0** is a Lean authority kernel with typed verdicts, composition rules, and meta-theorems for admissible transition. Not a sequent calculus, not a process calculus, not a proof-theoretic admissibility logic — see the scope fence in [`LeanProofs/Admissibility/README.md`](LeanProofs/Admissibility/README.md) for the full list of non-claims.

Importing `LeanProofs.Admissibility.CalculusOne` brings the eight 1.0 modules into scope (`Authority`, `StateTransition`, `Derivation`, `Execution`, `Corrective`, `Freshness`, `SurfaceAuthorization`, `WitnessInvariance`). Seven specimen consumers live in `LeanProofs.Admissibility.Examples`, demonstrating the public API.

> Calculus 1.0 models when evidence-backed claims may authorize transitions, proves that boundary-crossing upgrades are impossible by construction, and refuses laundering across the surface, freshness, witness, and authority axes.

Annex modules (recovery doctrine, cross-boundary specimens, numerical/artifact-kind axes, experimental composition) and root-level consumer specimens (Paper 24/25, NQ-shaped modules) build green but are not part of the 1.0 compatibility claim. All Admissibility modules are now wired into root and covered by `lake build`; per-module roles are tracked in [`LeanProofs/Admissibility/README.md`](LeanProofs/Admissibility/README.md).

## What this is not

This is not a complete formal model of institutions, platforms, incidents, or distributed systems.

It is not a general-purpose process calculus.

When a theorem lands here, it means a specific invalid inference has been isolated tightly enough to be checked mechanically.

## Companion repos

- **Papers repo:** [`unpingable/papers`](https://github.com/unpingable/papers) — prose papers, working notes, primitives, and the research-program structure. The paper-side crosswalk at [`docs/formalization-index.md`](https://github.com/unpingable/papers/blob/main/docs/formalization-index.md) inverts this repo's view (paper → module).
- **This repo (Lean):** admissibility kernel modules, formal claim register for Δt-paper claims, proof attempts, corrected theorem statements, and the BROKEN / STALE / SOUND audit. Module → paper crosswalk lives in [`PAPER-MAP.md`](PAPER-MAP.md).

## Audit harness for the Δt framework

The audit-harness layer translates selected claims from the [Δt framework](https://github.com/unpingable/papers) into Lean so they can be checked against explicit definitions instead of persuasive prose. The framework's prose papers make claims about how complex systems degrade, recover, misread themselves, or substitute proxies for reality.

Some claims survive. Some narrow. Some break.

That is the point. Lean is used here as a pressure chamber for theory: it helps distinguish structural claims from slogans that were useful for discovery but too loose to carry formal weight. Failed claims are kept as evidence of where the original prose overreached — see [`CLAIM-REGISTER.md`](CLAIM-REGISTER.md) for the BROKEN / STALE / SOUND / OPEN audit. The repo's value is less the surviving theorems than the disciplined damage report on the rest.

### Paper-anchored modules

**`LeanProofs/TaxonomyGraph.lean`** — Formal encoding of the cybernetic failure taxonomy (15 domains, 14 primitive + 1 composite). Encodes the pipeline graph, role classifications, and reinforcing loops as separate relations. Proves reachability, terminality, role distinctness, and decomposition claims. Cashes out into Paper 15 (sharpen + expose looseness), with secondary tie-ins to P16 and P22.

**`LeanProofs/BranchSelector.lean`** — Dual-budget closure-family selection. Budget asymmetry / priming / susceptibility. Cashes out into Paper 9 (certify + sharpen).

**`LeanProofs/PersistenceModel.lean`** — Five-state Δc→Δh dynamics. Cumulative rollback depletion under detached commits; three-way recovery distinction. Quantitative-burn + trace-realization cluster (added 2026-05-08): closed-form `commitsToHysteretic` commit count; non-strict and strict commit-count monotonicity (strict requires positive capacity above the per-commit burn unit); realization bridge from closed-form arithmetic to actual `run`-trace semantics; trace-level *post-repair faster* doctrine theorem composing the strict inequality with two applications of the realization bridge. Cashes out into Paper 18 (sharpen + bridge; Appendix A v1.1 candidate).

**`LeanProofs/OpsMasking.lean`** — Operational masking, case (i) projection clause. Pointwise-equal projected actions produce identical trajectories. Cashes out into Paper 23 (bridge + certify).

**`LeanProofs/Paper24SharedVision.lean`** — Algebraic shard for Paper 24's §4 metric probes. Sign correction on Proposition 2.

**`LeanProofs/RepairOperator.lean`** — Sovereign repair operator. No paper anchor; formalizes the working note `working/sovereign-repair-operator.md`.

**`LeanProofs/Admissibility.lean`** — P27 obligation skeleton (namespace `P27`). Sorry-free as of 2026-05-01 (three real proofs against the local `admissible` definition; two `True`-placeholder discharges with deferred-real-statement docstrings pending substrate-accusation / causal-binding predicates). Intentionally **not** wired into `LeanProofs.lean` root. Sibling but independent from the `Admissibility/*` kernel modules; the P27 skeleton is post-transition obligation accounting, the kernel is pre-action authorization.

### First result

**(2026-04-02):** The informal claim "Δh is the universal sink" is false as a pipeline reachability claim. Δs and Δk cannot reach Δh through pipeline edges. The "universal sink" property is a dynamic/temporal attractor claim, not a graph-topological one. The prose was compressing two different kinds of claims into one sentence. See `NOTES.md` for details.

## Building

Requires [elan](https://github.com/leanprover/elan) and Lean 4.

```bash
lake build
```

## Cross-references

- [`LeanProofs/Admissibility/README.md`](LeanProofs/Admissibility/README.md) — full module-by-module reference for the admissibility kernel modules
- [`WHAT-THE-LEAN-STACK-PROVES.md`](WHAT-THE-LEAN-STACK-PROVES.md) — module-level exposition of what each proof establishes and what it rules out
- [`PAPER-MAP.md`](PAPER-MAP.md) — module → paper crosswalk (which Lean modules cash out into which preprints, and whether the mapping is paper-ready)
- [`CLAIM-REGISTER.md`](CLAIM-REGISTER.md) — claim-level audit with specific prose-location status (BROKEN / STALE / SOUND / OPEN)
- Papers repo: [`docs/formalization-index.md`](https://github.com/unpingable/papers/blob/main/docs/formalization-index.md) — paper → module inverse view

## Status

All root-imported modules build. **Sorry-free as of 2026-05-08.** No theorems are currently admitted via `sorry`.

The previously-admitted investigative null `corrective_then_forward_is_not_monotone` (formerly in `LeanProofs/Admissibility/Corrective.lean`) was replaced by a positive boundary result in `LeanProofs/Admissibility/CorrectiveBoundary.lean`: the abstract kernel's existential remains formally undecidable in current vocabulary, but a parallel miniature kernel exhibits both possible answers — identity store ops + arbitrary env make the existential FALSE; nondegenerate ops + verdict-sensitive derivation make it TRUE. The abstract kernel is consistent with both, which is the doctrinally-correct stance. See [`CLAIM-REGISTER.md`](CLAIM-REGISTER.md) entries A1 (resolved) and #14 (boundary result) for the audit trail. **The discipline that previously displayed the sorry now displays the resolution path** — admitted-statement history is part of the public record, not erased once resolved.

Other open questions — what the kernel does *not* yet rule out — are tracked alongside the proofs themselves: `CorrectiveMonotone` is currently vacuously satisfiable at the abstract kernel level pending behavioral laws on `applyUpdate` / `appendGap` / `appendRevocation` (the boundary module supplies the model-dependence story without forcing the abstract kernel to commit); environment mutation (replacing the evaluator rather than the state) is a separate laundering vector outside `WeaklyLessPermissive`'s scope. See [`NOTES.md`](NOTES.md) and the per-module pinned-questions blocks for the rest.

## Reading the proofs

This repository is the canonical formal source. Required CI verifies that the formalization builds (`lean-action` on push); proof correctness rests on the Lean source itself, not on any rendered artifact.

The human-readable entry point for proof readers is this README plus the three companion documents linked under *Cross-references* above (`LeanProofs/Admissibility/README.md`, `WHAT-THE-LEAN-STACK-PROVES.md`, `CLAIM-REGISTER.md`).

The papers-side companion at `docs/formalization-index.md` in the [papers repo](https://github.com/unpingable/papers) inverts the view (paper → module).

GitHub Pages renders this README at <https://unpingable.github.io/lean/> via classic Pages, so the proof reader's portal is reachable from the web without additional infrastructure. Generated `doc-gen4` API HTML is not currently published; if added later it will sit as a secondary reference layer beneath the human-readable portal, not as the front door. Proof CI proves the formalization; publication of any rendered API docs would belong to a separate non-required workflow.
