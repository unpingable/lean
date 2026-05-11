# Admissibility — Authority kernel

Five core modules forming a Governor-neutral authority kernel, plus two boundary-result siblings (`CorrectiveBoundary.lean`, `WitnessInvariance.lean`). **No paper anchor** — this is *infrastructure substrate* for a future Governor (`agent_gov`) implementation citation, not a paper-claim cashout.

Sibling file `../Admissibility.lean` is the **P27 obligation skeleton** (namespace `P27`) — independent from the five kernel modules below. The P27 skeleton is post-transition obligation accounting; the kernel is pre-action authorization. Complementary, not duplicate. As of 2026-05-01 the P27 skeleton is `sorry`-free (three real proofs against the local `admissible` definition; two `True`-placeholder discharges with deferred-real-statement docstrings pending substrate-accusation / causal-binding predicates). Intentionally unwired; sorry-elimination does not imply wiring.

## Modules

### Layer 0 — `Authority.lean`

Verdict algebra: `authorityVerdict : Basis × Precedence × Standing → AuthorityVerdict`. **Authorized iff all three dimensions green.** Pure — no stores, no actors, no mutation. Direct parameters (no half-evaluated `Transition` struct).

### Layers 3a + 3b — `StateTransition.lean`

Governance state partitioned into four orthogonal stores (`PolicyStore`, `EvidenceStore`, `GapStore`, `RevocationStore`). `Step` inductive with one constructor per mutation kind; `applyStep` mutates exactly one store per Step.

**Trapdoor invariant: only `Step.amendPolicy` can touch `PolicyStore`.** Layer 3b adds `StepAllowed` (per-step standing predicate gating raw mutation) and the `executeIfAllowed` wrapper. Even authorized non-amendment cannot mutate `PolicyStore`.

### Layer 2 — `Derivation.lean`

Read-side bridge from `GovState × Actor × AuthorityClaim` to component verdicts. Bundled-structure design: `BasisDerivation` etc. carry both the function (`deriveBasis`) **and** its proof obligations (`revoked_never_admissible`) — concrete implementations must discharge spec at construction. One revocation-shaped safety consequence (`revoked_basis_never_authorized`).

### Layer 4 — `Execution.lean`

Combines mutation standing (`StepAllowed`) with claim authorization (`decideAuthority`). `AuthorizedStep env state actor` is a structure that bundles a `Step` with *both* permission proofs by construction — no half.

**Load-bearing theorem:** `revoked_basis_cannot_be_authorized_step` — if a claim's basis is revoked, no `AuthorizedStep` for that step can exist. Plus four lifted store-isolation theorems through `executeAuthorizedStep`.

### Layer 5 — `Corrective.lean` (added 2026-05-01)

Monotonicity layer over the existing four. Classifies every `Step` as `corrective`, `forward`, or `neutral` via a total `classify` function — adding a new `Step` constructor without an arm is a Lean non-exhaustive-match error, which is the enforcement surface against silently-corrective-and-authority-granting transitions.

`WeaklyLessPermissive env Γ' Γ` is the preorder "every claim authorized at Γ' was already authorized at Γ" (reflexive, transitive). `CorrectiveMonotone env` is a structure carrying the proof obligation that corrective Steps preserve `≼` — concrete evaluators discharge it at construction; no global axiom.

`RecoveryEnv` bundles a `DerivationEnv` with a `CorrectiveMonotone` witness; `applyCorrectiveRecovery` is the recovery-facing applier whose type signature *requires* a `RecoveryEnv` rather than a raw `DerivationEnv`. This is the available-vs-operationally-required distinction: the kernel makes monotonicity expressible; `RecoveryEnv` makes it non-optional at the recovery boundary. Analysis tools, audit tools, and forward-authorization paths still take raw `DerivationEnv`.

**Load-bearing corollary:** `corrective_no_authority_laundering` — for the same basis K, a corrective Step cannot turn a non-authorized claim into an authorized one. Same-K is load-bearing; re-entry through a fresh K' via a forward Step is exactly the legitimate path. Plus `corrective_sequence_monotone` (recovery flows are sequences) and `recovery_monotone` (the bundle-projected version).

Companion working note: `~/git/papers/working/admissible-recovery-semantics.md`.

### Sibling — `WitnessInvariance.lean` (added 2026-05-08)

**Boundary primitive module.** Formalizes the four-tier ladder
(selectivity / specialization / encapsulation / modularity) from the gnat-claude / ChatGPT / DeepSeek 2026-05-08 distillation of McGee, Zhang, Blank 2026 (*Cognitive Science* 50(3), "Evidence Against Syntactic Encapsulation in Large Language Models"). The doctrine is *prove the boundary claim, not the Wiley paper.*

Two namespaces:

- `Admissibility.WitnessInvariance` — three layered forms:
  - **Relational:** abstract `Encapsulated` / `MovesUnderExcludedPerturbation` over a `sameAdmittedBasis` equivalence relation, plus boundary theorem `moves_implies_not_encapsulated`.
  - **Typed perturbation-bounded** *(ChatGPT refinement, 2026-05-08):* `EncapsulatedWrt` / `MovesUnderDisturbance` parameterized by an *allowed-perturbation relation* on the disturbance class — *not* just a type. Refinement-monotonicity corollary `encapsulated_wrt_mono`; bridge theorem `encapsulated_wrt_iff_relational`.
  - **Regime-bounded** *(ChatGPT follow-on patch, 2026-05-08):* `EncapsulatedWithinRegime` / `MovesWithinRegime` adding an operating regime as a predicate on `ProductWorld`. Boundary theorem `moves_within_regime_implies_not_encapsulated_within_regime`. Universal-regime collapse theorem (`encapsulated_within_universal_regime_iff_encapsulated_wrt`) shows the regime layer is a strict generalization. Regime-monotonicity (`encapsulated_within_regime_mono`) — narrowing the regime preserves encapsulation, widening can break it.
- `Admissibility.WitnessInvarianceToy` — concrete two-bit toy (`ToyState` with `synBit`, `semBit` fields; `ToyWitness := synBit && semBit`) exhibiting `selectivity_does_not_imply_encapsulation`. The `synBit` / `semBit` field-name abbreviations work around the Lean 4 reserved keyword `syntax`.

Companion working note (papers repo): `~/git/papers/working/primitives/witness-invariance-failure.md`. Keeper: *Specialization is a gain pattern. Encapsulation is an invariance claim. Modularity is an earned boundary.* Operational corollary: *A witness that moves when the wrong variable moves is not lying. It is unqualified.*

The primitive supplies the missing rung in the admissibility apparatus's witness-validation vocabulary: NQ / Cadence / Continuity / Custody / Standing / Governor check construction discipline, freshness, authority — but did not previously have an explicit invariance-under-excluded-perturbation primitive. Now they do.

### Sibling — `CorrectiveBoundary.lean` (added 2026-05-07)

**Boundary-result module.** Not part of the five-module kernel proper; constructs a parallel miniature kernel with concrete payload types (`PolicyStore := List Nat`, etc.) and parameterized store ops, and proves model-dependence of the recorded null `corrective_then_forward_is_not_monotone`.

The previous `sorry`-bearing investigative null in `Corrective.lean` has been removed; the theorem statement is preserved as a comment-shape pointing here.

Two namespaces inside this module exhibit the model-dependence:

- `Identity` — store ops are identity functions. Proves `corrective_then_forward_is_monotone_universally`: under any env, the corrective-then-forward existential is FALSE.
- `Witness` — nondegenerate ops + a verdict-sensitive `BasisDerivation` that reads `policyStore` and `revocationStore`. Proves `corrective_then_forward_is_not_monotone`: a concrete witness `(initialState, recordRevocation 999, amendPolicy 1)` makes `WeaklyLessPermissive` fail at claim `1`.

The abstract `NondegenerateStoreSemantics` structure packages the three commitments from `papers/working/nondegenerate-store-semantics.md` (nontrivial store effects, verdict-sensitive derivation, mixed-class witness), and `corrective_then_forward_is_not_monotone_of_nondegenerate` proves the existential follows from the structure. `witness_satisfies_nondegenerate` verifies the witness model satisfies the structure; `witness_corrective_then_forward_is_not_monotone_via_abstract` recovers the witness theorem from the abstract path as a regression check.

The abstract kernel itself remains consistent with both the existential and its negation — that is the doctrinally-correct stance. The boundary module exhibits both possible answers without forcing the abstract kernel to commit. CLAIM-REGISTER #14 records the boundary result; A1 (the formerly-admitted sorry) is resolved.

## What the kernel warrants

> Governance-state mutation requires both mutation standing and an authorized claim verdict, and a revoked basis cannot produce an executable authorized step. Recovery-classified transitions cannot increase the authorized action set; authority-increasing recovery requires a separately classified forward transition with fresh basis.

## What it does NOT warrant

- Concrete `claimForStep` resolution (deferred to Governor instantiation; ontology bait if pre-committed).
- Concrete `AuthorityClaim` schema (kept abstract).
- Behavioral laws on the abstract store API (`appendEvidence`, `applyUpdate`, etc.) — they're `axiom`s with no behavioral constraints. The structural partition invariant survives, but no concrete claim about *what* a receipt records.
- Bridge between `Derivation.deriveStanding` (standing to *invoke* a claim) and `StateTransition.*Standing` predicates (standing to *mutate* governance state). Distinct standing concepts; not bridged yet.

## Build

All five kernel modules plus `CorrectiveBoundary` and `WitnessInvariance` are wired into `LeanProofs.lean` root. `lake build` (no args) regression-checks them as part of the default proof gate. Repo is sorry-free as of 2026-05-08.

```bash
lake build LeanProofs.Admissibility.Authority
lake build LeanProofs.Admissibility.StateTransition
lake build LeanProofs.Admissibility.Derivation
lake build LeanProofs.Admissibility.Execution
lake build LeanProofs.Admissibility.Corrective
lake build LeanProofs.Admissibility.CorrectiveBoundary
lake build LeanProofs.Admissibility.WitnessInvariance
```

Or just `lake build` for the whole stack.
