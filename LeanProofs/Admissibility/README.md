# Admissibility — Authority kernel

Five core modules forming a Governor-neutral authority kernel, plus nine siblings: two boundary-result modules (`CorrectiveBoundary.lean`, `WitnessInvariance.lean`) and seven admissibility-axis / refusal-gate kernels (`FiatAdmissibility.lean`, `NumericalAdmissibility.lean`, `SurfaceAuthorization.lean`, `PublicReceiptRefinement.lean`, `ClosureEligibility.lean`, `RecoveryMargin.lean`, `Freshness.lean`). **No paper anchor** — this is *infrastructure substrate* for a future Governor (`agent_gov`) implementation citation, not a paper-claim cashout.

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

### Sibling — `FiatAdmissibility.lean` (added 2026-05-11)

**Third admissibility axis: artifact-kind × use-kind.** Distinct from the authority-basis × state-mutation axis (`Authority` + `StateTransition`) and the witness × invariance axis (`WitnessInvariance`). Total `classify : ArtifactKind → UseKind → Classification`; every (kind, use) pair receives an explicit verdict (`allowed`, `requiresMediation`, `denied`, or `outOfScope`). The `outOfScope` verdict makes the kernel's silence audible — cases the kernel does not pretend to govern do not silently default. Closure property: no orphan corridors through which an artifact can claim a license it does not earn.

Keeper: *The admissibility kernel is itself admissible only under custody.*

Governs the relation between artifact kinds (axiom, definition, theorem, heuristic, metaphor, prestige token, proxy metric) and use kinds (orient, suggest, citeOrient, citeSupport, derive, authorize, mutateState, measureMagnitude). State mutation is the domain of the sibling `StateTransition` kernel; `FiatAdmissibility` does not pretend to govern it. Composition lemmas with the other admissibility kernels are explicitly deferred.

### Sibling — `NumericalAdmissibility.lean` (added 2026-05-12)

**Numerical-kind axis sibling to `FiatAdmissibility`.** Prevents one numerical kind from being treated as another: a score (constructed scalar with no native units) read as a quantity (measured magnitude); a rank (ordinal with no metric structure) read as value; a confidence (model's report about its own uncertainty) read as truth. Total `classify : NumericalKind → NumericalUse → Classification`; same closure-property shape as `FiatAdmissibility`.

Keeper: *A number's shape on the page does not license what the number can be asked to do.*

Sharper: *Score cannot imply magnitude; confidence cannot imply truth.* Rank, confidence, and probability cannot imply substrate at all; score, quantity, and proportion can reach substrate only through explicit mediation (calibration chain, measurement custody, population structure). Value claims always require utility structure for any non-quantity kind. Selection-by-extreme is never benign at the kernel layer. Several cells that look like keeper denials are mediation cells in disguise — value claims from any non-quantity kind require utility structure, so they discharge as `requiresMediation`, not `denied`.

### Sibling — `SurfaceAuthorization.lean` (added 2026-05-11)

**Governor-facing refusal gate.** Sibling to the root-level `LeanProofs/CollapsedSurface.lean` (the discrete-finite negative kernel proving a collapsed surface cannot identify cause). This module adds the *authorization* consequence: a collapsed surface cannot authorize cause-specific consequence without discriminating evidence.

Keeper: *A collapsed surface may authorize inquiry. It may not authorize attribution.*

Governor-shaped form: *Cause-specific authority requires discriminating evidence.* Encodes the refusal gate (collapsed + cause-specific + no discriminator ⇒ deny). Does not encode the recovery machinery itself — `Breaker` is an abstract enum naming the three known recovery paths (preserved history, independent measurement, admissible perturbation); the predicates that constitute each kind remain unformalized here. Recovery doctrine lives in the sibling `PublicReceiptRefinement.lean`.

### Sibling — `PublicReceiptRefinement.lean` (added 2026-05-12)

**Recovery doctrine companion to `SurfaceAuthorization`.** Formalizes the simplest recovery channel: a public receipt refines an observation when it both excludes some cause the surface alone would admit *and* remains consistent with at least one surface-admitted cause.

Keeper: *Refinement narrows the admissible-cause set without collapsing it to empty.*

A receipt that excludes every cause is contradiction, not refinement. A receipt that excludes nothing is decoration, not refinement. Honest refinement lives between these two failure modes. Refinement does not, in general, identify a unique cause — narrowing is not identification. Abstract over receipt type and admittance predicate; concrete receipt schemas live in consuming systems (Governor's receipt schema, Paper 24's receipt-lineage discussion, NQ's witness intake). The other two recovery channels named in `SurfaceAuthorization`'s `Breaker` enum (independent measurement, admissible perturbation) remain abstract.

### Sibling — `ClosureEligibility.lean` (added 2026-05-12)

**Refusal kernel for closure verdicts on shift-bounded operations.** Invariant proved: `closure ⇔ (survived ∧ resolved ∧ slack-available)`. Any deficit on any of the three dimensions forces handoff or incident.

Keeper: *Survival is a handoff condition, not a closure condition.*

Sharper: *A survived shift with unresolved threat or depleted operator slack must emit handoff, not closure.* Same family resemblance as the admissibility-decay candidates: a visible outcome is being asked to license a substantive claim it does not, by itself, support. Sibling to `RecoveryMargin` (which governs within-interval visible-vs-capacity; this module governs end-of-interval survival-vs-closure). Sibling to `SurfaceAuthorization` (both encode refusal gates over claims given insufficient discriminating evidence). Nightshift-style operational doctrines are the obvious downstream consumer.

### Sibling — `RecoveryMargin.lean` (added 2026-05-11)

**Refusal kernel for the gap between a visible liveness signal and underlying recovery capacity.** Proves `VisibleGreen` and `RecoveryMargin` are independent predicates — the visible surface cannot serve as a witness for capacity.

Keeper: *Visible green does not entail recovery margin.*

In tightly-coupled, high-cost-of-deviation environments, a system can maintain visible status by sacrificing recovery capacity, and the dashboard cannot report the second condition. Discrete observation-equivalence specimen at the dashboard layer (see `LeanProofs/CollapsedSurface.lean` for the general cause-from-render kernel and Paper 25 for the matrix/dynamical version). NQ-style witness-standing findings are the obvious downstream consumer (where the dashboard is being asked to testify about operability, not just status).

### Sibling — `Freshness.lean` (added 2026-05-19)

**Metric-time admissibility axis.** Sibling to the kernel's existing ordinal-time apparatus (Step sequences, `WeaklyLessPermissive` preorder, `ClosureEligibility.NoRegress` pairs, `RevocationStore` evolution). Where the ordinal apparatus answers *"did this happen before that,"* `Freshness` answers *"is this timestamp within an acceptable window."*

Keeper: *Expired evidence cannot prove current standing. Future-issued evidence cannot prove current standing. Incoherent intervals cannot prove standing. Excessive clock divergence makes the assessment unsafe.*

Three positive predicates compose into `Fresh`: `TemporallyCoherent` (issued precedes expires), `DivergenceAcceptable` (verifier-issuer clock divergence within bound), `WithinValidity` (now falls inside skewed validity window). Five negative theorems mirror four of Standing's nine `AssessmentResult` verdict kinds: `expired_not_fresh` / `not_yet_valid_not_fresh` mirror `Expired` / `NotYetValid`; `incoherent_not_fresh` and `not_precedes_not_fresh` cover the two structurally-distinct failure modes of `TemporallyCoherent` under opaque `Time.le` (both map to `AssessmentCompromised`); `divergence_excessive_not_fresh` mirrors the other `AssessmentCompromised` branch. The fifth temporal verdict (`ReplayDetected`) stays in the kernel's ordinal apparatus.

Canonical consumer: `~/git/standing` (workload-identity / grant authorization tool, production-quality Rust). Forcing receipt: Standing's `AssessmentResult::AssessmentCompromised` is exactly the kernel's "gap" verdict applied to metric-time admissibility — and the Lean kernel previously could not express that the gap was *temporal* rather than basis-, precedence-, or standing-shaped. This module closes that asymmetry.

Time is kept opaque (`axiom Time : Type` + four axiomatic operations: `le`, `add`, `sub`, `absSub`). Concretizing to `Nat`/`Int` would leak structural facts into theorems and break the abstraction over real consumer types (chrono's `DateTime<Utc>`). Composition with the other admissibility kernels is explicitly deferred — same defer-marker pattern as `FiatAdmissibility`. Not `Δt.lean`.

## What the kernel warrants

> Governance-state mutation requires both mutation standing and an authorized claim verdict, and a revoked basis cannot produce an executable authorized step. Recovery-classified transitions cannot increase the authorized action set; authority-increasing recovery requires a separately classified forward transition with fresh basis.

## What it does NOT warrant

- Concrete `claimForStep` resolution (deferred to Governor instantiation; ontology bait if pre-committed).
- Concrete `AuthorityClaim` schema (kept abstract).
- Behavioral laws on the abstract store API (`appendEvidence`, `applyUpdate`, etc.) — they're `axiom`s with no behavioral constraints. The structural partition invariant survives, but no concrete claim about *what* a receipt records.
- Bridge between `Derivation.deriveStanding` (standing to *invoke* a claim) and `StateTransition.*Standing` predicates (standing to *mutate* governance state). Distinct standing concepts; not bridged yet.

## Build

All fourteen modules are wired into `LeanProofs.lean` root. `lake build` (no args) regression-checks them as part of the default proof gate. Repo is sorry-free as of 2026-05-19 (the two `sorry` strings in `Corrective.lean` and `CorrectiveBoundary.lean` are docstring references to a resolved former-`sorry`, not proof holes).

```bash
lake build LeanProofs.Admissibility.Authority
lake build LeanProofs.Admissibility.StateTransition
lake build LeanProofs.Admissibility.Derivation
lake build LeanProofs.Admissibility.Execution
lake build LeanProofs.Admissibility.Corrective
lake build LeanProofs.Admissibility.CorrectiveBoundary
lake build LeanProofs.Admissibility.WitnessInvariance
lake build LeanProofs.Admissibility.FiatAdmissibility
lake build LeanProofs.Admissibility.NumericalAdmissibility
lake build LeanProofs.Admissibility.SurfaceAuthorization
lake build LeanProofs.Admissibility.PublicReceiptRefinement
lake build LeanProofs.Admissibility.ClosureEligibility
lake build LeanProofs.Admissibility.RecoveryMargin
lake build LeanProofs.Admissibility.Freshness
```

Or just `lake build` for the whole stack.
