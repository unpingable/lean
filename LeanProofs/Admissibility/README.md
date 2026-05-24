# Admissibility — Authority kernel

This directory contains the original five-module authority kernel (`Authority`, `StateTransition`, `Derivation`, `Execution`, `Corrective`) plus sibling axes and specimens. **Calculus 1.0** exposes an eight-module public surface via `CalculusOne.lean` (the five-module kernel plus `Freshness`, `SurfaceAuthorization`, and `WitnessInvariance`). The remainder — two further boundary-result modules, four other axis / refusal-gate kernels, four cross-boundary artifact specimens, and two experimental composition slices — sits in the annex (still in this directory, not in the 1.0 promise). **No paper anchor** — this is *infrastructure substrate* for a future Governor (`agent_gov`) implementation citation, not a paper-claim cashout.

Sibling file `../Admissibility.lean` is the **P27 obligation skeleton** (namespace `P27`) — independent from the five kernel modules below. The P27 skeleton is post-transition obligation accounting; the kernel is pre-action authorization. Complementary, not duplicate. As of 2026-05-01 the P27 skeleton is `sorry`-free (three real proofs against the local `admissible` definition; two `True`-placeholder discharges with deferred-real-statement docstrings pending substrate-accusation / causal-binding predicates). Intentionally unwired; sorry-elimination does not imply wiring.

## Changelog

### 1.0.1 — 2026-05-24 (patch)

Fixes:
- Repair `CrossBoundaryCascade` parse error (`Step.exposeFromExposure` constructor body: multi-line `insert (...)` inside a structure update required parentheses to terminate cleanly).

Infrastructure:
- Wire all Admissibility modules into `LeanProofs.lean` (full set: twenty-three modules including the previously-unwired four `CrossBoundary*` specimens and the two experimental `Composition` / `LocalBoundary` modules).
- `lake build` (no args) now covers the full stack, preventing silent unwired-module failures.

No public surface change. No slogan change. `CalculusOne.lean` remains the 1.0 public surface.

> 1.0.1 strengthens regression coverage without changing the 1.0 public surface.

### 1.0 — 2026-05-24

Initial named public surface. Eight modules in `CalculusOne.lean`: `Authority`, `StateTransition`, `Derivation`, `Execution`, `Corrective`, `Freshness`, `SurfaceAuthorization`, `WitnessInvariance`. Seven specimen consumers in `Examples.lean`. Slogan, scope-fence, and annex documented in this README.

## Calculus 1.0 — public surface

`CalculusOne.lean` is the named public aggregator. Importing it brings the 1.0 surface into scope. Eight modules are tagged `[1.0]` and form the compatibility claim:

| Module                | Role                                              |
| --------------------- | ------------------------------------------------- |
| `Authority`           | Verdict algebra; five blocking theorems           |
| `StateTransition`     | Four-store governance algebra; trapdoor invariant |
| `Derivation`          | Read-side bridge: state + claim → verdict         |
| `Execution`           | Composition: both proofs by construction          |
| `Corrective`          | Classification + monotonicity + recovery gate     |
| `Freshness`           | Metric-time axis; five negative theorems          |
| `SurfaceAuthorization`| Collapsed-surface refusal; cause-specific gate    |
| `WitnessInvariance`   | Evidence-stability discipline under perturbation  |

Slogan:

> Admissibility Calculus 1.0 models when evidence-backed claims may authorize transitions, proves that boundary-crossing upgrades are impossible by construction, and refuses laundering across the surface, freshness, witness, and authority axes.

Seven specimen consumers live in `Examples.lean` (imports `CalculusOne`): valid advisory result, valid authorized mutation, stale evidence refusal, self-cert denial, conflicting precedence denial, receipt-without-authority non-upgrade, open finding accounted.

## Scope fence — what 1.0 does NOT claim

1. 1.0 does not prove a general theory of institutions.
2. 1.0 does not claim recovery doctrine. Recovery sits in the annex via `PublicReceiptRefinement` and `RecoveryMargin`.
3. 1.0 does not claim cross-boundary process composition. The `CrossBoundary*` family is annex.
4. 1.0 does not claim numerical-kind or artifact-kind axes. `NumericalAdmissibility`, `FiatAdmissibility`, `AxisSkew` are annex.
5. 1.0 does not claim a calculus of communicating processes. `Composition` and `LocalBoundary` are experimental.
6. 1.0 does not claim formal verification of any real-world institution, system, or paper. Root-level consumer modules (`Paper24SharedVision`, `Paper25EpistemicBorderControl`, `TaxonomyGraph`, `BranchSelector`, `OpsMasking`, `RepairOperator`, `CollapsedSurface`, `Basic`, `PersistenceModel`, the P27 skeleton at `../Admissibility.lean`) are specimens, not contents.

## Annex — compiled, not promised

Annex modules are green and sorry-free but are not part of the 1.0 compatibility claim. Future versions may rename, refactor, or absorb them without prior notice.

| Module                       | Role                                                      |
| ---------------------------- | --------------------------------------------------------- |
| `CorrectiveBoundary`         | Model-dependence boundary result (parallel mini-kernel)   |
| `PublicReceiptRefinement`    | Recovery doctrine companion to `SurfaceAuthorization`     |
| `RecoveryMargin`             | Visible-vs-capacity gap refusal (within-interval)         |
| `ClosureEligibility`         | Survival-vs-closure refusal (end-of-interval)             |
| `FiatAdmissibility`          | Artifact-kind × use-kind axis                             |
| `NumericalAdmissibility`     | Numerical-kind × use-kind axis                            |
| `AxisSkew`                   | Directional comparison axis (lagging/matched/leading)     |
| `CrossBoundaryExposure`      | Cross-boundary exposure mint specimen                     |
| `CrossBoundaryDegradation`   | Cross-boundary degradation provenance specimen            |
| `CrossBoundaryFailureMint`   | Cross-boundary failure-to-exposure mint specimen          |
| `CrossBoundaryCascade`       | Cross-boundary cascade reachability specimen              |
| `Composition` `[experimental]` | Diagnostic: process syntax alone does not make a calculus |
| `LocalBoundary` `[experimental]` | Experimental aperture toward compositional calculus     |

## Modules

### Layer 0 — `Authority.lean` `[1.0]`

Verdict algebra: `authorityVerdict : Basis × Precedence × Standing → AuthorityVerdict`. **Authorized iff all three dimensions green.** Pure — no stores, no actors, no mutation. Direct parameters (no half-evaluated `Transition` struct).

### Layers 3a + 3b — `StateTransition.lean` `[1.0]`

Governance state partitioned into four orthogonal stores (`PolicyStore`, `EvidenceStore`, `GapStore`, `RevocationStore`). `Step` inductive with one constructor per mutation kind; `applyStep` mutates exactly one store per Step.

**Trapdoor invariant: only `Step.amendPolicy` can touch `PolicyStore`.** Layer 3b adds `StepAllowed` (per-step standing predicate gating raw mutation) and the `executeIfAllowed` wrapper. Even authorized non-amendment cannot mutate `PolicyStore`.

### Layer 2 — `Derivation.lean` `[1.0]`

Read-side bridge from `GovState × Actor × AuthorityClaim` to component verdicts. Bundled-structure design: `BasisDerivation` etc. carry both the function (`deriveBasis`) **and** its proof obligations (`revoked_never_admissible`) — concrete implementations must discharge spec at construction. One revocation-shaped safety consequence (`revoked_basis_never_authorized`).

### Layer 4 — `Execution.lean` `[1.0]`

Combines mutation standing (`StepAllowed`) with claim authorization (`decideAuthority`). `AuthorizedStep env state actor` is a structure that bundles a `Step` with *both* permission proofs by construction — no half.

**Load-bearing theorem:** `revoked_basis_cannot_be_authorized_step` — if a claim's basis is revoked, no `AuthorizedStep` for that step can exist. Plus four lifted store-isolation theorems through `executeAuthorizedStep`.

### Layer 5 — `Corrective.lean` `[1.0]` (added 2026-05-01)

Monotonicity layer over the existing four. Classifies every `Step` as `corrective`, `forward`, or `neutral` via a total `classify` function — adding a new `Step` constructor without an arm is a Lean non-exhaustive-match error, which is the enforcement surface against silently-corrective-and-authority-granting transitions.

`WeaklyLessPermissive env Γ' Γ` is the preorder "every claim authorized at Γ' was already authorized at Γ" (reflexive, transitive). `CorrectiveMonotone env` is a structure carrying the proof obligation that corrective Steps preserve `≼` — concrete evaluators discharge it at construction; no global axiom.

`RecoveryEnv` bundles a `DerivationEnv` with a `CorrectiveMonotone` witness; `applyCorrectiveRecovery` is the recovery-facing applier whose type signature *requires* a `RecoveryEnv` rather than a raw `DerivationEnv`. This is the available-vs-operationally-required distinction: the kernel makes monotonicity expressible; `RecoveryEnv` makes it non-optional at the recovery boundary. Analysis tools, audit tools, and forward-authorization paths still take raw `DerivationEnv`.

**Load-bearing corollary:** `corrective_no_authority_laundering` — for the same basis K, a corrective Step cannot turn a non-authorized claim into an authorized one. Same-K is load-bearing; re-entry through a fresh K' via a forward Step is exactly the legitimate path. Plus `corrective_sequence_monotone` (recovery flows are sequences) and `recovery_monotone` (the bundle-projected version).

Companion working note: `~/git/papers/working/admissible-recovery-semantics.md`.

### Sibling — `WitnessInvariance.lean` `[1.0]` (added 2026-05-08)

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

### Sibling — `CorrectiveBoundary.lean` `[annex]` (added 2026-05-07)

**Boundary-result module.** Not part of the five-module kernel proper; constructs a parallel miniature kernel with concrete payload types (`PolicyStore := List Nat`, etc.) and parameterized store ops, and proves model-dependence of the recorded null `corrective_then_forward_is_not_monotone`.

The previous `sorry`-bearing investigative null in `Corrective.lean` has been removed; the theorem statement is preserved as a comment-shape pointing here.

Two namespaces inside this module exhibit the model-dependence:

- `Identity` — store ops are identity functions. Proves `corrective_then_forward_is_monotone_universally`: under any env, the corrective-then-forward existential is FALSE.
- `Witness` — nondegenerate ops + a verdict-sensitive `BasisDerivation` that reads `policyStore` and `revocationStore`. Proves `corrective_then_forward_is_not_monotone`: a concrete witness `(initialState, recordRevocation 999, amendPolicy 1)` makes `WeaklyLessPermissive` fail at claim `1`.

The abstract `NondegenerateStoreSemantics` structure packages the three commitments from `papers/working/nondegenerate-store-semantics.md` (nontrivial store effects, verdict-sensitive derivation, mixed-class witness), and `corrective_then_forward_is_not_monotone_of_nondegenerate` proves the existential follows from the structure. `witness_satisfies_nondegenerate` verifies the witness model satisfies the structure; `witness_corrective_then_forward_is_not_monotone_via_abstract` recovers the witness theorem from the abstract path as a regression check.

The abstract kernel itself remains consistent with both the existential and its negation — that is the doctrinally-correct stance. The boundary module exhibits both possible answers without forcing the abstract kernel to commit. CLAIM-REGISTER #14 records the boundary result; A1 (the formerly-admitted sorry) is resolved.

### Sibling — `FiatAdmissibility.lean` `[annex]` (added 2026-05-11)

**Third admissibility axis: artifact-kind × use-kind.** Distinct from the authority-basis × state-mutation axis (`Authority` + `StateTransition`) and the witness × invariance axis (`WitnessInvariance`). Total `classify : ArtifactKind → UseKind → Classification`; every (kind, use) pair receives an explicit verdict (`allowed`, `requiresMediation`, `denied`, or `outOfScope`). The `outOfScope` verdict makes the kernel's silence audible — cases the kernel does not pretend to govern do not silently default. Closure property: no orphan corridors through which an artifact can claim a license it does not earn.

Keeper: *The admissibility kernel is itself admissible only under custody.*

Governs the relation between artifact kinds (axiom, definition, theorem, heuristic, metaphor, prestige token, proxy metric) and use kinds (orient, suggest, citeOrient, citeSupport, derive, authorize, mutateState, measureMagnitude). State mutation is the domain of the sibling `StateTransition` kernel; `FiatAdmissibility` does not pretend to govern it. Composition lemmas with the other admissibility kernels are explicitly deferred.

### Sibling — `NumericalAdmissibility.lean` `[annex]` (added 2026-05-12)

**Numerical-kind axis sibling to `FiatAdmissibility`.** Prevents one numerical kind from being treated as another: a score (constructed scalar with no native units) read as a quantity (measured magnitude); a rank (ordinal with no metric structure) read as value; a confidence (model's report about its own uncertainty) read as truth. Total `classify : NumericalKind → NumericalUse → Classification`; same closure-property shape as `FiatAdmissibility`.

Keeper: *A number's shape on the page does not license what the number can be asked to do.*

Sharper: *Score cannot imply magnitude; confidence cannot imply truth.* Rank, confidence, and probability cannot imply substrate at all; score, quantity, and proportion can reach substrate only through explicit mediation (calibration chain, measurement custody, population structure). Value claims always require utility structure for any non-quantity kind. Selection-by-extreme is never benign at the kernel layer. Several cells that look like keeper denials are mediation cells in disguise — value claims from any non-quantity kind require utility structure, so they discharge as `requiresMediation`, not `denied`.

### Sibling — `SurfaceAuthorization.lean` `[1.0]` (added 2026-05-11)

**Governor-facing refusal gate.** Sibling to the root-level `LeanProofs/CollapsedSurface.lean` (the discrete-finite negative kernel proving a collapsed surface cannot identify cause). This module adds the *authorization* consequence: a collapsed surface cannot authorize cause-specific consequence without discriminating evidence.

Keeper: *A collapsed surface may authorize inquiry. It may not authorize attribution.*

Governor-shaped form: *Cause-specific authority requires discriminating evidence.* Encodes the refusal gate (collapsed + cause-specific + no discriminator ⇒ deny). Does not encode the recovery machinery itself — `Breaker` is an abstract enum naming the three known recovery paths (preserved history, independent measurement, admissible perturbation); the predicates that constitute each kind remain unformalized here. Recovery doctrine lives in the sibling `PublicReceiptRefinement.lean`.

### Sibling — `PublicReceiptRefinement.lean` `[annex]` (added 2026-05-12)

**Recovery doctrine companion to `SurfaceAuthorization`.** Formalizes the simplest recovery channel: a public receipt refines an observation when it both excludes some cause the surface alone would admit *and* remains consistent with at least one surface-admitted cause.

Keeper: *Refinement narrows the admissible-cause set without collapsing it to empty.*

A receipt that excludes every cause is contradiction, not refinement. A receipt that excludes nothing is decoration, not refinement. Honest refinement lives between these two failure modes. Refinement does not, in general, identify a unique cause — narrowing is not identification. Abstract over receipt type and admittance predicate; concrete receipt schemas live in consuming systems (Governor's receipt schema, Paper 24's receipt-lineage discussion, NQ's witness intake). The other two recovery channels named in `SurfaceAuthorization`'s `Breaker` enum (independent measurement, admissible perturbation) remain abstract.

### Sibling — `ClosureEligibility.lean` `[annex]` (added 2026-05-12)

**Refusal kernel for closure verdicts on shift-bounded operations.** Invariant proved: `closure ⇔ (survived ∧ resolved ∧ slack-available)`. Any deficit on any of the three dimensions forces handoff or incident.

Keeper: *Survival is a handoff condition, not a closure condition.*

Sharper: *A survived shift with unresolved threat or depleted operator slack must emit handoff, not closure.* Same family resemblance as the admissibility-decay candidates: a visible outcome is being asked to license a substantive claim it does not, by itself, support. Sibling to `RecoveryMargin` (which governs within-interval visible-vs-capacity; this module governs end-of-interval survival-vs-closure). Sibling to `SurfaceAuthorization` (both encode refusal gates over claims given insufficient discriminating evidence). Nightshift-style operational doctrines are the obvious downstream consumer.

### Sibling — `RecoveryMargin.lean` `[annex]` (added 2026-05-11)

**Refusal kernel for the gap between a visible liveness signal and underlying recovery capacity.** Proves `VisibleGreen` and `RecoveryMargin` are independent predicates — the visible surface cannot serve as a witness for capacity.

Keeper: *Visible green does not entail recovery margin.*

In tightly-coupled, high-cost-of-deviation environments, a system can maintain visible status by sacrificing recovery capacity, and the dashboard cannot report the second condition. Discrete observation-equivalence specimen at the dashboard layer (see `LeanProofs/CollapsedSurface.lean` for the general cause-from-render kernel and Paper 25 for the matrix/dynamical version). NQ-style witness-standing findings are the obvious downstream consumer (where the dashboard is being asked to testify about operability, not just status).

### Sibling — `Freshness.lean` `[1.0]` (added 2026-05-19)

**Metric-time admissibility axis.** Sibling to the kernel's existing ordinal-time apparatus (Step sequences, `WeaklyLessPermissive` preorder, `ClosureEligibility.NoRegress` pairs, `RevocationStore` evolution). Where the ordinal apparatus answers *"did this happen before that,"* `Freshness` answers *"is this timestamp within an acceptable window."*

Keeper: *Expired evidence cannot prove current standing. Future-issued evidence cannot prove current standing. Incoherent intervals cannot prove standing. Excessive clock divergence makes the assessment unsafe.*

Three positive predicates compose into `Fresh`: `TemporallyCoherent` (issued precedes expires), `DivergenceAcceptable` (verifier-issuer clock divergence within bound), `WithinValidity` (now falls inside skewed validity window). Five negative theorems mirror four of Standing's nine `AssessmentResult` verdict kinds: `expired_not_fresh` / `not_yet_valid_not_fresh` mirror `Expired` / `NotYetValid`; `incoherent_not_fresh` and `not_precedes_not_fresh` cover the two structurally-distinct failure modes of `TemporallyCoherent` under opaque `Time.le` (both map to `AssessmentCompromised`); `divergence_excessive_not_fresh` mirrors the other `AssessmentCompromised` branch. The fifth temporal verdict (`ReplayDetected`) stays in the kernel's ordinal apparatus.

Canonical consumer: `~/git/standing` (workload-identity / grant authorization tool, production-quality Rust). Forcing receipt: Standing's `AssessmentResult::AssessmentCompromised` is exactly the kernel's "gap" verdict applied to metric-time admissibility — and the Lean kernel previously could not express that the gap was *temporal* rather than basis-, precedence-, or standing-shaped. This module closes that asymmetry.

Time is kept opaque (`axiom Time : Type` + four axiomatic operations: `le`, `add`, `sub`, `absSub`). Concretizing to `Nat`/`Int` would leak structural facts into theorems and break the abstraction over real consumer types (chrono's `DateTime<Utc>`). Composition with the other admissibility kernels is explicitly deferred — same defer-marker pattern as `FiatAdmissibility`. Not `Δt.lean`.

### Sibling — `CrossBoundaryExposure.lean` `[annex]` (added 2026-05-21)

**Cross-boundary exposure mint specimen.** First brick in the cross-boundary artifact-specimen sub-family. Introduces a first-class `Exposure` artifact carrying `(origin, target, failure)` provenance and an operator-supplied `BoundaryPartition` (`Internal` / `External` Prop-valued predicates over abstract `Domain`). The only constructor that can add an exposure is `Step.expose`, and it requires `Boundary.authorized e.origin e.target = true`.

Keeper: *Boundary authorization is the exposure mint.*

Sharper: This is the exposure layer. Not damage. Not failure leakage. Not cascade. Not internal failure. Failure is not modeled here.

Theorem `no_external_exposure_without_authorized_edge` — under a boundary that authorizes no Internal→External edges, no reachable configuration can contain an exposure with Internal origin and External target. Proof technique is the same forward-closed-set invariant idiom used in `TaxonomyGraph` lane proofs; the novelty is the first-class artifact (`Exposure`) and the abstract boundary-partition layer, not the proof family. `Reach.trans` lives here as a utility lemma used by downstream sibling slices that project their reachability into this kernel.

Origin: outside-aperture audit (fresh-context model asked "is this a process calculus?") surfaced the candidate; inside-aperture kernel-overlap audit demoted/reparented the work from a proposed `Delta/` family into this `Admissibility/CrossBoundary*` sub-family. See `papers/working/cross-boundary-artifact-specimens.md` for the audit trail.

### Sibling — `CrossBoundaryDegradation.lean` `[annex]` (added 2026-05-21)

**Cross-boundary degradation-provenance specimen.** Second brick. Extends the exposure kernel with a `degrade` action carrying a `Cause`: either `direct` (external trigger, no exposure precondition) or `fromExposure e` (which requires `e ∈ c.exposures ∧ e.target = d` as constructor arguments). Direct degradation is licensed; *exposure-attributed* degradation cannot fabricate provenance.

Keeper: *This is degradation provenance only. Not damage. Not failure leakage. Not cascade.*

Theorem `no_external_degradation_from_internal_exposure` — under a sealed boundary, no reachable configuration can take a `degrade_fromExposure` step on an External domain whose cited exposure has Internal origin. Direct corollary of `CrossBoundaryExposure.no_external_exposure_without_authorized_edge`, lifted through the projection pattern (richer `Config` with `grades : Domain → Grade`, `toExposureConfig` projection stripping the grade map, per-step projection lemma, `Reach.trans` chaining).

`Grade` is kept abstract; the provenance theorem is independent of grade semantics, so `initGrade : Grade` is an explicit parameter rather than an `Inhabited` instance. Grade-side dynamics (recovery, hysteresis, capability) belong on the persistence side, not in the `CrossBoundary*` family.

### Sibling — `CrossBoundaryFailureMint.lean` `[annex]` (added 2026-05-21)

**Cross-boundary failure-to-exposure mint specimen.** Third brick. Introduces `FailureEvent (domain, failure)` as a first-class recorded artifact and a two-rule step relation: `fail d f` records a failure event with no boundary precondition (failure is a local-domain event), and `exposeFromFailure e` mints an exposure requiring *both* (a) `⟨e.origin, e.failure⟩ ∈ c.failures` (a recorded precedent) *and* (b) `B.authorized e.origin e.target = true` (boundary authorization).

Keeper: *Failure is not exposure. Failure can be recorded without crossing a boundary. Exposure from failure is minted only by boundary authorization.*

Two theorems:

- `no_exposeFromFailure_internal_to_external` (step-local) — a single `exposeFromFailure` step from an Internal origin to an External target is impossible under a sealed boundary. Direct from the constructor's authorization precondition; no `Reach` required.
- `no_external_exposure_from_internal_failure` (reachable-config) — no reachable configuration of the failure-mint system can contain an Internal-origin External-target exposure. Lifted via projection through the exposure kernel.

This is the rung that makes the English sentence presentable: *internal failure → recorded failure event → authorized exposure mint → (later) downstream consequence*. Each arrow is a constructor or theorem application; no prose glue.

### Sibling — `CrossBoundaryCascade.lean` `[annex]` (added 2026-05-21)

**Cross-boundary cascade reachability specimen.** Fourth brick; the first *affirmative* theorem in the cross-boundary family. Introduces an abstract `AuthorizedPath (B : Boundary Domain) : Domain → Domain → Prop` inductive (two constructors: `edge` for single authorized hops, `cons` for chained ones) and a third step rule `Step.exposeFromExposure` that propagates an existing exposure to a fresh immediate-origin exposure across one authorized edge.

Keeper: *Cascade is authorized exposure reachability. Not inevitability. Not degradation. Not damage. Not recovery.*

**Immediate-origin discipline.** Each cascade hop mints `Exposure(d_prev, d_next, f)` whose `origin / target` are the *immediate* boundary crossing, not the ultimate failure source. This is what makes projection to the kernel clean — every minted exposure satisfies `B.authorized origin target = true` directly. If ultimate provenance is ever needed, a separate `CascadeChain` witness can be added later; do not overload `Exposure.origin` to mean both "immediate crossing origin" and "root cause."

Theorem `authorized_path_permits_endpoint_exposure` — given an `AuthorizedPath B d₀ dₙ` and a failure kind `f`, there *exists* a reachable cascade configuration containing some exposure to `dₙ` carrying failure `f`. Bootstrap: `Step.fail d₀ f` then `Step.exposeFromFailure ⟨d₀, d_first_hop, f⟩`, then chain `Step.exposeFromExposure` along the path. Existential, not inevitable; the theorem statement uses *permits* / *reachable* / *exists*, never *will* / *must* / *eventually*.

Composition with the rest: `step_to_exposure_reach` projects all three cascade actions to kernel reachability (`fail` → `Reach.refl`; both `expose*` rules → a single `Step.expose`). A local `Reach.trans` on cascade's own `Reach` chains the inductive-helper's bootstrap step with its IH-derived reach. No `CrossBoundaryDegradation` import — cascade is exposure propagation, not degradation.

Scope fence: no scheduling, no fairness, no rates, no `TaxonomyGraph`, no process syntax. *Topology, not selection.* If a future slice adds `EnabledStep` / `SchedulerAllows` / `ScheduledReach`, it lives in a separate `CrossBoundaryScheduling.lean`.

### Composition discipline — projection pattern

The cross-boundary trio shares a single composition discipline that lets each downstream brick reuse the kernel containment theorem without reproving it. Each brick:

1. **Defines a richer `Config`** carrying the kernel's exposure set plus whatever new artifacts the brick introduces (degradation grades; failure events). The exposure set field is identical in name and type to the kernel's.
2. **Defines `toExposureConfig : Config → CrossBoundaryExposure.Config`** as projection that drops the new artifacts and preserves the exposure set. Definitionally `rfl` between the projected initial config and the kernel's initial config.
3. **Proves `step_to_exposure_reach`** — each step in the richer relation projects to a `CrossBoundaryExposure.Reach`. Steps that don't touch exposures project to `Reach.refl`; steps that mint exposures project to a single kernel `Step.expose` with the same authorization argument.
4. **Proves `reach_to_exposure_reach`** — chains per-step projections via `CrossBoundaryExposure.Reach.trans`.
5. **Invokes the kernel containment theorem** `no_external_exposure_without_authorized_edge` on the projected reach. The brick's own theorem then falls out as a direct corollary or a step-local strengthening.

Schematic:

```text
richer Config
  ↓ toExposureConfig
kernel Config
  ↓ step_to_exposure_reach + Reach.trans
kernel Reach (initialConfig → toExposureConfig c)
  ↓ no_external_exposure_without_authorized_edge
no forbidden exposure in toExposureConfig c
  ↓ (toExposureConfig c).exposures = c.exposures (rfl)
no forbidden exposure in c
```

The discipline is what makes the bricks composable: any future cross-boundary slice (cascade, monitoring, etc.) can inherit containment by following the same five steps. Adding a new step constructor that bypasses the boundary check would break `step_to_exposure_reach` immediately — the kernel forces the discipline at the type level.

Audit provenance and a detailed walk-through live in `papers/working/cross-boundary-artifact-specimens.md`. The two-tracks rule (kernel-specimen track now; process-calculus / composition track deferred until forced) is filed in operator memory as `feedback-kernel-vs-process-calculus`.

## What the kernel warrants

> Governance-state mutation requires both mutation standing and an authorized claim verdict, and a revoked basis cannot produce an executable authorized step. Recovery-classified transitions cannot increase the authorized action set; authority-increasing recovery requires a separately classified forward transition with fresh basis.

## What it does NOT warrant

- Concrete `claimForStep` resolution (deferred to Governor instantiation; ontology bait if pre-committed).
- Concrete `AuthorityClaim` schema (kept abstract).
- Behavioral laws on the abstract store API (`appendEvidence`, `applyUpdate`, etc.) — they're `axiom`s with no behavioral constraints. The structural partition invariant survives, but no concrete claim about *what* a receipt records.
- Bridge between `Derivation.deriveStanding` (standing to *invoke* a claim) and `StateTransition.*Standing` predicates (standing to *mutate* governance state). Distinct standing concepts; not bridged yet.

## Build

All twenty-three Admissibility modules are wired into `LeanProofs.lean` root (twenty-one kernel/sibling modules + `CalculusOne` aggregator + `Examples` specimens). The default `lake build` (no args) regression-checks the entire set as the default proof gate. Nothing is silently unwired.

Public-surface gate: `lake build LeanProofs.Admissibility.CalculusOne` builds the aggregator; `lake build LeanProofs.Admissibility.Examples` exercises the specimen consumers through the public API.

No Lean proof holes as of 2026-05-24 in the wired stack. The word `sorry` does appear in docstring text within `Corrective.lean` and `CorrectiveBoundary.lean` as references to a resolved former-`sorry`; these are comments, not proof holes — a plain grep will find them.

### Cascade repair note

`CrossBoundaryCascade.lean` had a pre-existing parse error in its `Step.exposeFromExposure` constructor (multi-line `insert (...)` inside a structure update not parsing without parentheses). The fix was two characters; the file is now wired and covered by the default `lake build`. This bug had been silent since 2026-05-21 because the module was unwired.

All modules below are wired into root and covered by `lake build` (no args). Individual builds are listed for narrow regression checks.

```bash
# Public 1.0 surface (aggregator + specimens)
lake build LeanProofs.Admissibility.CalculusOne
lake build LeanProofs.Admissibility.Examples

# Core kernel [1.0]
lake build LeanProofs.Admissibility.Authority
lake build LeanProofs.Admissibility.StateTransition
lake build LeanProofs.Admissibility.Derivation
lake build LeanProofs.Admissibility.Execution
lake build LeanProofs.Admissibility.Corrective
lake build LeanProofs.Admissibility.Freshness
lake build LeanProofs.Admissibility.SurfaceAuthorization
lake build LeanProofs.Admissibility.WitnessInvariance

# Annex — axis & refusal kernels
lake build LeanProofs.Admissibility.CorrectiveBoundary
lake build LeanProofs.Admissibility.FiatAdmissibility
lake build LeanProofs.Admissibility.NumericalAdmissibility
lake build LeanProofs.Admissibility.PublicReceiptRefinement
lake build LeanProofs.Admissibility.ClosureEligibility
lake build LeanProofs.Admissibility.RecoveryMargin
lake build LeanProofs.Admissibility.AxisSkew

# Annex — cross-boundary artifact specimens
lake build LeanProofs.Admissibility.CrossBoundaryExposure
lake build LeanProofs.Admissibility.CrossBoundaryDegradation
lake build LeanProofs.Admissibility.CrossBoundaryFailureMint
lake build LeanProofs.Admissibility.CrossBoundaryCascade

# Annex — experimental composition
lake build LeanProofs.Admissibility.Composition
lake build LeanProofs.Admissibility.LocalBoundary
```
