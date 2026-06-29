# Lean Proofs

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.20369489.svg)](https://doi.org/10.5281/zenodo.20369489)

Small, auditable Lean 4 formalizations for reasoning about evidence, standing, freshness, authority, witnessed transition, and the boundaries between them.

## Current release: 1.4.0 — Witnessed Derivation Calculus

**1.4.0** promotes the ratified **Witnessed Derivation Calculus** into the canonical public surface as the Mathlib-free `LeanProofs.Witnessed.*` library.

It provides:

- a witnessed-derivation judgment, `Lift`;
- paid composition and multi-context cut;
- soundness, provenance, and revocation non-manufacture results (schematic);
- a canonical-form normalization theorem for the canonical freshness embedding;
- a separate four-axis model-admission filter, `WitnessedDiscipline` (`bridge_valid` / `semantic_nontrivial` / `bridge_selective` / `properly_live`);
- a factorization showing the former `Discriminating` axis contributes no independent information beyond `SemanticNontrivial` under `BridgeValid`.

The name is deliberately narrow. This is **not** a process calculus, a maximal admissibility logic, or a unification of every kernel in the repository. The calculus governs witnessed derivation across typed bridges; `WitnessedDiscipline` is a model filter beside it, not part of normalization, and normalization itself is scoped to the canonical freshness embedding.

The ratified calculus lives in the canonical surface as `LeanProofs.Witnessed.*` — a separate **Mathlib-free** library (`import LeanProofs.Witnessed`), with its axiom footprint regression-gated by `scripts/check-witnessed-footprint.sh`. Its ratified source is preserved under `experiments/no_free_lift_wiring/`. This is a **new, additive** public surface and does **not** alter the stable 1.x **Admissibility Kernels** surface — which is why it ships as the **minor** release **1.4.0**, not a major bump. The planning docs frame this as "the 2.0 boundary" ([`V2.0-EXIT-CRITERIA.md`](experiments/no_free_lift_wiring/V2.0-EXIT-CRITERIA.md)); semver keeps its one job (nothing in 1.x breaks), and the milestone lives in the release title and notes. A future **2.0** is reserved for a *structural* strengthening of the calculus — see the "What Would Make This 2.0" gate in [`docs/WITNESSED-FRONTIER-REGISTER.md`](docs/WITNESSED-FRONTIER-REGISTER.md).

- **Exact ratified claims and theorem receipts:** [`RATIFICATION-v1.3.md`](experiments/no_free_lift_wiring/RATIFICATION-v1.3.md)
- **Migration and divergence constraints:** [`MIGRATION-NOTES.md`](experiments/no_free_lift_wiring/MIGRATION-NOTES.md)
- **2.0 public-promotion exit criteria:** [`V2.0-EXIT-CRITERIA.md`](experiments/no_free_lift_wiring/V2.0-EXIT-CRITERIA.md)
- **Release:** `v1.4.0` (supersedes [`v1.3.0-rc1`](https://github.com/unpingable/lean/releases/tag/v1.3.0-rc1))

## Stable public surface: Admissibility Kernels

The stable public surface remains a collection of small admissibility kernels, each isolating a particular refusal boundary: stale authority, invalid standing upgrades, unauthorized transition, collapsed public surfaces, unwitnessed movement, and related category errors.

> Local kernels decide admissibility. Witnessed movement between contexts requires an explicit bridge.

The repository therefore contains two related but distinct layers:

1. **Admissibility Kernels** — small local refusal kernels (the stable 1.x public surface).
2. **Witnessed Derivation Calculus** — the ratified calculus for witnessed movement and composition across typed bridges, a canonical **Mathlib-free** surface (`LeanProofs.Witnessed.*`) shipped in 1.4.0.

Neither is a universal model of institutions, software systems, or agency.

## Start here

- **What changed in v1.3** → [`RATIFICATION-v1.3.md`](experiments/no_free_lift_wiring/RATIFICATION-v1.3.md)
- **Plain-English project explainer** → [`WHAT-THIS-IS.md`](WHAT-THIS-IS.md). No formal-methods background assumed.
- **A single kernel walked end-to-end** → [`docs/worked-examples/standing-upgrade-block.md`](docs/worked-examples/standing-upgrade-block.md). What it refuses and why.
- **What the current Lean stack proves** → [`WHAT-THIS-PROVES.md`](WHAT-THIS-PROVES.md)
- **Full admissibility-kernel reference** → [`LeanProofs/Admissibility/README.md`](LeanProofs/Admissibility/README.md)
- **Project root, author, full preprint list** → [unpingable.github.io](https://unpingable.github.io/). The [papers repo](https://github.com/unpingable/papers) is the prose home; this repo is the formal audit harness for the Δt research series.

## How to read this repository

Most modules follow the same discipline:

1. define a small model of a boundary or failure surface;
2. state the invalid inference the system must not allow;
3. prove that the inference cannot be derived under that model;
4. leave implementation, policy, and world-level consequence outside the theorem.

The point is not to prove an entire software system correct. It is to make invalid promotions and unpaid boundary crossings mechanically visible before they become architecture.

## Map

- **Authority kernels** — authority, standing, verdicts, state transition, execution, corrective layers.
- **Surface / receipt / witness kernels** — collapsed surfaces, public receipt refinement, witness invariance.
- **Admissibility axes** — artifact kind, numerical kind, closure, recovery margin, freshness.
- **Cross-boundary artifact specimens** — exposure, degradation, failure minting, cascade.
- **Safety-bridge family** *(Frontier 1)* — proves that authorization does not entail defended-value preservation; a separate bridge predicate is required. Ratifies the standalone safety axis, not any unified-calculus rename.
- **Witnessed Derivation Calculus** *(ratified; canonical `LeanProofs.Witnessed.*` since 1.4.0, Mathlib-free)* — witnessed movement and composition across typed bridges. See the release section above.

For the full module-by-module reference, see [`LeanProofs/Admissibility/README.md`](LeanProofs/Admissibility/README.md).

## Stable 1.x public surface

> **The Lean work did not produce a *unified* calculus. It produced a set of small admissibility kernels, each isolating a different refusal boundary — and, in v1.3, a narrow witnessed-derivation calculus beside them.**

The stable public surface (**Admissibility Kernels**, unchanged since 1.0) is a Lean authority kernel with typed verdicts and object-level refusal theorems for admissible transition. General composition rules and meta-theorems are out of scope for the 1.x stable surface and live in separate kernel families. Not a sequent calculus, not a process calculus, not a proof-theoretic admissibility logic, not a unified maximal calculus — see the scope fence in [`LeanProofs/Admissibility/README.md`](LeanProofs/Admissibility/README.md) for the full list of non-claims.

Importing `LeanProofs.Admissibility.AdmissibilityKernels` brings the eight stable modules into scope (`Authority`, `StateTransition`, `Derivation`, `Execution`, `Corrective`, `Freshness`, `SurfaceAuthorization`, `WitnessInvariance`). Seven specimen consumers live in `LeanProofs.Admissibility.Examples`, demonstrating the public API.

> Admissibility Kernels models when evidence-backed claims may authorize transitions, proves that boundary-crossing upgrades are impossible by construction, and refuses laundering across the surface, freshness, witness, and authority axes.

(Migration note: this aggregator was previously named `CalculusOne` under an "Admissibility Calculus 1.0" framing. The rename retires "calculus" from the *stable* public surface; the Witnessed Derivation Calculus reintroduces it only for that narrow witnessed-derivation object. Namespace `Admissibility.CalculusOne` is now `Admissibility.Kernels`; the marker theorem `calculus_one_compiles` is now `kernels_compile`.)

## Repository custody and compatibility

Annex modules (recovery doctrine, cross-boundary specimens, numerical/artifact-kind axes, experimental composition, safety-bridge family) and root-level consumer specimens (Paper 24/25, NQ-shaped modules) build green but are not part of the stable compatibility claim. Thirty-four of the forty-seven modules in `LeanProofs/Admissibility/` are wired into `LeanProofs.lean` for regression coverage (9 PUBLIC-SHIPPED, 24 ANNEX, 1 DEPRECATED shim); the remaining thirteen are fenced UNRATIFIED-CANDIDATE / SCRATCH material that builds only when invoked directly. Wiring is build-coverage, not public-surface promotion — promotion lives in the `AdmissibilityKernels.lean` aggregator's import list. Per-file custody status is regression-checked via `scripts/check-custody-classes.sh`; per-module roles are tracked in [`LeanProofs/Admissibility/README.md`](LeanProofs/Admissibility/README.md).

### `experiments/` — tracked wiring witnesses (non-canonical)

The `experiments/` tree holds reproducible integration artifacts that are **not imported by the canonical proof surface** — each is its own Lake project with its own toolchain pin. A successful build under `experiments/` attests that the wiring checks; it does **not** promote any result into the relied-upon theorem surface (build-exit-0 is attestation of the math, never admission of a world claim). See [`experiments/README.md`](experiments/README.md) for the per-project custody contract (`EXPERIMENTAL-WIRING`).

Currently: `no_free_lift_wiring/` — the customs-office spine plus modeled freshness/authority embeddings. It hosts the **ratified source** of the Witnessed Derivation Calculus (`Successor/` + the `Wired` spine) — now promoted into the canonical surface as `LeanProofs.Witnessed.*` (this tree remains the provenance record, still not imported by the canonical surface) — and the **findings record for the retired composition-classification gate** ([`COMPOSITION-CLASSIFICATION-TARGET.md`](experiments/no_free_lift_wiring/COMPOSITION-CLASSIFICATION-TARGET.md) — the proposed exhaustive classifier was investigated and retired as the wrong target, not unproved). The public-surface promotion was governed by [`V2.0-EXIT-CRITERIA.md`](experiments/no_free_lift_wiring/V2.0-EXIT-CRITERIA.md): public promotion, migration map, stable namespace, and a non-experimental compiled consumer — not new theorems. That promotion shipped in 1.4.0.

## What this is not

This is not a complete formal model of institutions, platforms, incidents, or distributed systems.

It is not a general-purpose process calculus.

When a theorem lands here, it means a specific invalid inference has been isolated tightly enough to be checked mechanically.

## Companion repos

- **Papers repo:** [`unpingable/papers`](https://github.com/unpingable/papers) — prose papers, working notes, primitives, and the research-program structure. The paper-side crosswalk at [`docs/formalization-index.md`](https://github.com/unpingable/papers/blob/main/docs/formalization-index.md) inverts this repo's view (paper → module).
- **This repo (Lean):** admissibility kernel modules, the witnessed-derivation calculus, the formal claim register for Δt-paper claims, proof attempts, corrected theorem statements, and the BROKEN / STALE / SOUND audit. Module → paper crosswalk lives in [`PAPER-MAP.md`](PAPER-MAP.md).

## Audit harness for the Δt framework

The audit-harness layer translates selected claims from the [Δt framework](https://github.com/unpingable/papers) into Lean so they can be checked against explicit definitions instead of persuasive prose. The framework's prose papers make claims about how complex systems degrade, recover, misread themselves, or substitute proxies for reality. It is one consumer of the admissibility kernels, not the whole repo.

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

### First documented BROKEN claim

The audit's first recorded finding, kept here as the chronological anchor for the BROKEN/STALE/SOUND register. Subsequent results — the Admissibility Kernels surface, the sorry-free kernel chain, and the cross-boundary specimens — are tracked in [`WHAT-THIS-PROVES.md`](WHAT-THIS-PROVES.md) and [`CLAIM-REGISTER.md`](CLAIM-REGISTER.md); gaps against the AGI-requirements doc live in [the closed 2026-05-10 reverse-gap audit](historical/audits/AGI_REQUIREMENTS_REVERSE_GAP_AUDIT_2026-05-10.md). Not appended here.

**(2026-04-02; refined 2026-06-29):** The informal claim "Δh is the universal sink" is false as a pipeline reachability claim. Δs and Δk cannot reach Δh through pipeline edges; the static graph instead decomposes into three terminal closure families `{Δg, Δa}`, `{Δx}`, `{Δh}` (Δh is *a* terminal family, not *the* sink). Any "universal sink" reading of Δh would be a *temporal-attractor* claim rather than a graph-topological one — and that temporal claim is **OPEN**: it requires an explicit dynamics substrate the static graph cannot represent (the placeholder axiom that once stood in for it was removed in v2.0.0). The prose was compressing two different kinds of claims into one sentence. See [`CLAIM-REGISTER.md`](CLAIM-REGISTER.md) #1 for the full status.

## Building

Requires [elan](https://github.com/leanprover/elan) and Lean 4.

```bash
lake build                  # stable Admissibility surface + Witnessed calculus + regression-wired modules
lake build Witnessed        # the Witnessed Derivation Calculus in isolation (Mathlib-free)
bash scripts/check-witnessed-footprint.sh   # re-attest the ratified WDC axiom footprint (fail-closed)
bash scripts/audit-axioms.sh                # repo axiom classifier (signature/interface-law/specimen; 0 forbidden)
bash scripts/audit-native-decide.sh         # native_decide confined to finite-witness modules
bash scripts/check-mathlib-pin.sh           # lakefile mathlib rev == manifest SHA (no silent drift)
```

**Custody posture: the repository is not axiom-free; it is *axiom-classified*. WDC promoted
receipts remain footprint-attested.** See [`docs/AUDIT-POLICY.md`](docs/AUDIT-POLICY.md) for
what each gate checks and the four axiom classes (signature / interface-law / specimen /
forbidden — the last held at zero).

The ratified source of the calculus also builds standalone under
`experiments/no_free_lift_wiring/` (its own Lake project / toolchain pin) — that tree
is the provenance record, not the canonical import path.

## Cross-references

- [`LeanProofs/Admissibility/README.md`](LeanProofs/Admissibility/README.md) — full module-by-module reference for the admissibility kernel modules
- [`WHAT-THIS-PROVES.md`](WHAT-THIS-PROVES.md) — module-level exposition of what each proof establishes and what it rules out
- [`historical/audits/AGI_REQUIREMENTS_REVERSE_GAP_AUDIT_2026-05-10.md`](historical/audits/AGI_REQUIREMENTS_REVERSE_GAP_AUDIT_2026-05-10.md) — **closed audit artifact**: the dated 2026-05-10 AGI-requirements reverse-gap audit (gaps where *that one requirements document* demands more than the kernel delivers). Not the project's live open-problems register, not a promotion queue.
- [`PAPER-MAP.md`](PAPER-MAP.md) — module → paper crosswalk (which Lean modules cash out into which preprints, and whether the mapping is paper-ready)
- [`CLAIM-REGISTER.md`](CLAIM-REGISTER.md) — claim-level audit with specific prose-location status (BROKEN / STALE / SOUND / OPEN)
- [`RATIFICATION-v1.3.md`](experiments/no_free_lift_wiring/RATIFICATION-v1.3.md) — the ratified v1.3 claims with exact theorem receipts
- [`V2.0-EXIT-CRITERIA.md`](experiments/no_free_lift_wiring/V2.0-EXIT-CRITERIA.md) — public-promotion criteria for the 2.0 boundary
- Narrative walkthrough: [`docs/worked-examples/standing-upgrade-block.md`](docs/worked-examples/standing-upgrade-block.md)
- Papers repo: [`docs/formalization-index.md`](https://github.com/unpingable/papers/blob/main/docs/formalization-index.md) — paper → module inverse view

## Status

**`v1.4.0` released** — the Witnessed Derivation Calculus is now a canonical, Mathlib-free public surface at `LeanProofs.Witnessed.*`; the stable 1.x Admissibility Kernels surface is unchanged. All root-imported modules build. **Sorry-free as of 2026-05-28.** No theorems are currently admitted via `sorry`. Gaps surfaced by the dated 2026-05-10 AGI-requirements reverse-gap audit are recorded in [the closed reverse-gap audit](historical/audits/AGI_REQUIREMENTS_REVERSE_GAP_AUDIT_2026-05-10.md) — a **closed audit artifact** scoped to that one requirements document, not the project's live open-problems register.

The previously-admitted investigative null `corrective_then_forward_is_not_monotone` (formerly in `LeanProofs/Admissibility/Corrective.lean`) was replaced by a positive boundary result in `LeanProofs/Admissibility/CorrectiveBoundary.lean`: the abstract kernel's existential remains formally undecidable in current vocabulary, but a parallel miniature kernel exhibits both possible answers — identity store ops + arbitrary env make the existential FALSE; nondegenerate ops + verdict-sensitive derivation make it TRUE. The abstract kernel is consistent with both, which is the doctrinally-correct stance. See [`CLAIM-REGISTER.md`](CLAIM-REGISTER.md) entries A1 (resolved) and #14 (boundary result) for the audit trail. **The discipline that previously displayed the sorry now displays the resolution path** — admitted-statement history is part of the public record, not erased once resolved.

Other open questions — what the kernel does *not* yet rule out — are tracked alongside the proofs themselves: `CorrectiveMonotone` is currently vacuously satisfiable at the abstract kernel level pending behavioral laws on `applyUpdate` / `appendGap` / `appendRevocation` (the boundary module supplies the model-dependence story without forcing the abstract kernel to commit); environment mutation (replacing the evaluator rather than the state) is a separate laundering vector outside `WeaklyLessPermissive`'s scope. See [`NOTES.md`](NOTES.md) and the per-module pinned-questions blocks for the rest.

## Reading the proofs

This repository is the canonical formal source. Required CI verifies that the formalization builds (`lean-action` on push); proof correctness rests on the Lean source itself, not on any rendered artifact.

The human-readable entry point for proof readers is this README plus the companion documents linked under *Cross-references* above.

The papers-side companion at `docs/formalization-index.md` in the [papers repo](https://github.com/unpingable/papers) inverts the view (paper → module).

GitHub Pages renders this README at <https://unpingable.github.io/lean/> via classic Pages, so the proof reader's portal is reachable from the web without additional infrastructure. Generated `doc-gen4` API HTML is not currently published; if added later it will sit as a secondary reference layer beneath the human-readable portal, not as the front door.
