# Lean Proofs

*New here? See [unpingable.github.io](https://unpingable.github.io/) for the project root — author (James Beck), scope, and the full preprint list. This repo is the formal audit harness; the [papers repo](https://github.com/unpingable/papers) is the prose home. See also the [methodology page](https://github.com/unpingable/papers/blob/main/docs/methodology.md) for what the BROKEN / STALE / SOUND register is doing and why.*

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

**`LeanProofs/PersistenceModel.lean`** — Five-state Δc→Δh dynamics. Cumulative rollback depletion under detached commits; three-way recovery distinction. Quantitative-burn + trace-realization cluster (added 2026-05-08): closed-form `commitsToHysteretic` commit count; non-strict and strict commit-count monotonicity (strict requires positive capacity above the per-commit burn unit, since `cap = 0` and `cap = burnRate` both burn out on the first commit); realization bridge from closed-form arithmetic to actual `run`-trace semantics; trace-level *post-repair faster* doctrine theorem composing the strict inequality with two applications of the realization bridge. Full ladder: capacity arithmetic → commit-count horizon → strict-faster theorem → run-trace realized faster. Cashes out into Paper 18 (sharpen + bridge; Appendix A v1.1 candidate).

**`LeanProofs/OpsMasking.lean`** — Operational masking, case (i) projection clause. Pointwise-equal projected actions produce identical trajectories. Cashes out into Paper 23 (bridge + certify).

**`LeanProofs/Paper24SharedVision.lean`** — Algebraic shard for Paper 24's §4 metric probes. Sign correction on Proposition 2.

### Infrastructure substrate (no paper anchor)

**`LeanProofs/Admissibility/`** — Governor-neutral authority kernel. Five core modules: `Authority.lean` (verdict algebra), `StateTransition.lean` (partitioned governance state + `StepAllowed`), `Derivation.lean` (read-side bridge), `Execution.lean` (`AuthorizedStep` requires both mutation standing and claim verdict), `Corrective.lean` (corrective monotonicity layer — classify-based enforcement surface, `RecoveryEnv` gate). Plus two boundary-result siblings (added 2026-05-08): `CorrectiveBoundary.lean` builds a parallel miniature kernel and proves the corrective+forward existential is genuinely model-dependent (identity stores → false; nondegenerate stores + verdict-sensitive derivation → true), and `WitnessInvariance.lean` carries the admissibility-witness invariance discipline in three layered forms (relational, typed perturbation-bounded, regime-bounded) — companion to the witness-invariance-failure primitive at `papers/working/primitives/witness-invariance-failure.md`. Warrants: *governance-state mutation requires both mutation standing and an authorized claim verdict, and a revoked basis cannot produce an executable authorized step.* Corrective monotonicity is declared as an obligation shape (`CorrectiveMonotone env`) that any compliant `DerivationEnv` must discharge; the obligation is currently vacuously satisfiable at the abstract kernel level while behavioral laws on `applyUpdate` / `appendRevocation` / `appendGap` are unconstrained axioms, so the kernel pins the *shape* of the non-laundering claim but does not yet rule out laundering by any specific concrete env. The boundary module exhibits both possible answers in a parallel miniature kernel without committing the abstract kernel to either. See [`LeanProofs/Admissibility/README.md`](LeanProofs/Admissibility/README.md) for the per-module breakdown. Substrate for future Governor (`agent_gov`) implementation citation; not paper-claim cashout.

#### Why admissibility is different

The paper-anchored modules mostly test claims about Δt dynamics: failure taxonomies, persistence states, masking, shared vision, recovery margins, and trace behavior. They ask whether a prose claim about system behavior survives contact with explicit definitions.

The `Admissibility/` modules do something slightly different. They formalize the layer where evidence, standing, scope, freshness, and authorization determine whether a claim or transition is allowed to bind consequence at all.

In other words, these modules are not primarily asking:

> did the system fail?

They ask:

> is this claim, action, exposure, or state transition admissible under the rules that supposedly authorize it?

The recurring proof pattern is intentionally small: define the artifact, define its authorized constructor or mint, then prove that the forbidden version is unreachable or unconstructible. This is why the admissibility kernel sits as infrastructure substrate rather than as a single paper cashout: it supplies reusable machinery for ruling out specific laundering moves across later systems and papers.

Recent cross-boundary specimens extend that pattern to propagation artifacts:

- `CrossBoundaryExposure.lean` — boundary authorization is the exposure mint.
- `CrossBoundaryDegradation.lean` — degradation attributed to exposure must cite an active exposure.
- `CrossBoundaryFailureMint.lean` — internal failure can be recorded without becoming external exposure unless an authorized crossing exists.
- `CrossBoundaryCascade.lean` — an authorized path permits reachable endpoint exposure, existentially; it does not prove inevitability, scheduling, damage, or stochastic propagation.

These are not a full process calculus. They are small admissibility kernels: machine-checked proofs that specific forbidden cross-boundary artifacts cannot be constructed under the stated rules.

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

All root-imported modules build. **Sorry-free as of 2026-05-08.** No theorems are currently admitted via `sorry`.

The previously-admitted investigative null `corrective_then_forward_is_not_monotone` (formerly in `LeanProofs/Admissibility/Corrective.lean`) was replaced by a positive boundary result in `LeanProofs/Admissibility/CorrectiveBoundary.lean`: the abstract kernel's existential remains formally undecidable in current vocabulary, but a parallel miniature kernel exhibits both possible answers — identity store ops + arbitrary env make the existential FALSE; nondegenerate ops + verdict-sensitive derivation make it TRUE. The abstract kernel is consistent with both, which is the doctrinally-correct stance. See [`CLAIM-REGISTER.md`](CLAIM-REGISTER.md) entries A1 (resolved) and #14 (boundary result) for the audit trail. **The discipline that previously displayed the sorry now displays the resolution path** — admitted-statement history is part of the public record, not erased once resolved.

Other open questions — what the kernel does *not* yet rule out — are tracked alongside the proofs themselves: `CorrectiveMonotone` is currently vacuously satisfiable at the abstract kernel level pending behavioral laws on `applyUpdate` / `appendGap` / `appendRevocation` (the boundary module supplies the model-dependence story without forcing the abstract kernel to commit); environment mutation (replacing the evaluator rather than the state) is a separate laundering vector outside `WeaklyLessPermissive`'s scope. See [`NOTES.md`](NOTES.md) and the per-module pinned-questions blocks for the rest.

## Reading the proofs

This repository is the canonical formal source. Required CI verifies that the formalization builds (`lean-action` on push); proof correctness rests on the Lean source itself, not on any rendered artifact.

The human-readable entry point for proof readers is this README plus three companion documents:

- [`PAPER-MAP.md`](PAPER-MAP.md) — module → paper crosswalk
- [`CLAIM-REGISTER.md`](CLAIM-REGISTER.md) — claim-level audit (BROKEN / STALE / SOUND / OPEN per specific prose location)
- [`WHAT-THE-LEAN-STACK-PROVES.md`](WHAT-THE-LEAN-STACK-PROVES.md) — module-level exposition of what each proof establishes and what it rules out

The papers-side companion at `docs/formalization-index.md` in the [papers repo](https://github.com/unpingable/papers) inverts the view (paper → module).

GitHub Pages renders this README at <https://unpingable.github.io/lean/> via classic Pages, so the proof reader's portal is reachable from the web without additional infrastructure. Generated `doc-gen4` API HTML is not currently published; if added later it will sit as a secondary reference layer beneath the human-readable portal, not as the front door. Proof CI proves the formalization; publication of any rendered API docs would belong to a separate non-required workflow.
