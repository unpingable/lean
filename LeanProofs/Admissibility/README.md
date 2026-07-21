# Admissibility — Kernels, siblings, and the v14 Calculus

> **The original Admissibility Kernels 1.0 root did not earn the name
> "calculus"; it remains eight small refusal kernels. v14 separately earned
> the capital-C name for the exact object under `Admissibility.Calculus`.**

> **Development order:** formalization leads code. A consumer or runtime
> specimen is not permission to begin a theorem and is never a prerequisite
> for skunkworks formalization. Intrinsic theorem-shape,
> non-vacuity, overlap, and scope govern opening the formal work; proof and
> axiom checks govern its discharge. Custody promotion is a separate
> operator/release decision and may consider runtime evidence. Citation names
> an intended contract. Conformance always requires an explicit scope, an
> exact map of every governed distinction in that scope, executable
> preservation and transport evidence, and revision-bound qualification
> receipts. A formal refinement proof may strengthen covered obligations but
> does not waive those artifacts.

**Stable Admissibility surfaces.** The original eight-module 1.0 compatibility
claim remains aggregated by `AdmissibilityKernels.lean`: `Authority`,
`StateTransition`, `Derivation`, `Execution`, `Corrective`, `Freshness`,
`SurfaceAuthorization`, and `WitnessInvariance`. v13 also records the
already-coherent DynamicTrace pair, `SafetyBridge`, and PathVerdict as separate
exact stable families; none widens the eight-module 1.0 root. v14 adds the
separate exact `AdmissibilityCalculus` root and extends PathVerdict with the
rung-1 substrate.

**Current custody contract (v14 release).** Public source uses
`Custody-Class: PUBLIC-SHIPPED` plus `Surface-Role: STABLE-SURFACE` or
`PUBLIC-EVIDENCE`.  Stable status is the transitive closure of a registered
exact family root.  Finished examples, countermodels, applications, and audit
specimens are terminal public evidence outside those closures.  Live
incubation moves to the sibling skunkworks; `ANNEX`, `Scratch/`, and
`UNRATIFIED-CANDIDATE` are retired as live public-repository lanes.

Adding a public header or a build target does not promote a module.  Promotion
is an explicit operator decision recorded by the applicable exact root and
registry. The released v14 tree closes at 201 public Lean sources — 104 stable,
96 evidence, one aggregate — across eleven roots and 131 ownership relations.
The pending top-level Governed Transport admission candidate would extend that
inventory to 216/115/100/1 across twelve roots and 142 ownership relations;
it does not widen any existing Admissibility root. The completed release
receipt is in
[`../../docs/V14-RELEASE-LEDGER.md`](../../docs/V14-RELEASE-LEDGER.md).
The pending target record is
[`../../docs/GT4A-TARGET-CUSTODY-CANDIDATE_2026-07-20.md`](../../docs/GT4A-TARGET-CUSTODY-CANDIDATE_2026-07-20.md).

**What this is for.** Infrastructure substrate and formal contract, not by
itself a paper or runtime proof. Governor (`agent_gov`) and the consumer tools
listed below are correspondence targets; each runtime owns its exact map and
evidence.

(Migration note: the aggregator was previously `CalculusOne.lean` under an "Admissibility Calculus 1.0" framing. The rename is doctrine — the earlier artifact did not earn the name "Admissibility Calculus," and "calculus" overclaimed the shape of what it was. Namespace `Admissibility.CalculusOne` is now `Admissibility.Kernels`; the marker theorem `calculus_one_compiles` is now `kernels_compile`. The deprecated import shim shipped through v9 and was removed in v10.0.0; the eight-module kernel surface itself is unchanged. Revision at v14 rung 2, 2026-07-17: the term remains reserved for the unified object now being constructed under `Admissibility.Calculus` — that namespace is the construction's stable address, and its presence does not claim completion; the capital-C claim stays gated on the campaign's separately reviewed final ratification. Discharge at v14 rung 7, 2026-07-18: all seven rungs were admitted, custody closed, and the capital-C claim was then ratified as its own reviewed act — the object under `Admissibility.Calculus` is the **Admissibility Calculus**. The v10 correction stands as history: the name was withheld until earned, and the reservation is now discharged, not repealed.)

The v12 sibling file `../Admissibility.lean` was the **P27 obligation
skeleton** (namespace `P27`) — independent from the kernels below. It is
sorry-free but contains two `True`-placeholder discharges rather than the
missing substantive predicates, so its current canonical home is skunkworks
at `formalization/Calculi/Scratch/P27ObligationSkeleton.lean`. The public
original is deleted; green elaboration did not make it public evidence.

> **Architecture in one breath:** `AdmissibilityKernels` defines the original
> compatibility path. Public evidence contains **refusal kernels** — small
> formal countermodels that block recurring inadmissible witness moves (for
> example, `RecoveryMargin` blocks *visible green → recovery capacity* and
> `ConsolidationDenial` blocks *fluency → settlement*) without turning every
> specimen signature into stable API.

> **Legacy-kernel composition discipline:** the 1.0 kernels and their sibling
> families remain a typed federation; no implication between them is free.
> v14 relates only its named families through explicit governed instances,
> spines, comparison receipts, and stored-decision crossings. It does not erase
> the local bridge obligations of every other module.

## v14 current surface — Governed Admissibility Calculus

`LeanProofs.Admissibility.Calculus` is the exact public root of the ratified
capital-C **Admissibility Calculus**. The PathVerdict additions from rung 1 are
separately gated at 36 receipts; rungs 2–7 contribute 191 exact receipts to the
Calculus root.

| Campaign layer | Public modules / role |
| --- | --- |
| Rung 1 | `PathVerdict.Domains` and `PathVerdict.Located`: domain transport and carried-id diagnostics |
| Rung 2 | `Calculus.Core`: `GovernedFamily`, native evidence-returning `decide`, separate standing/custody/obligation books |
| Rung 3 | `Calculus.Instances.Weathering*` and `BoundedPaidReachability*`: two native no-distortion instances |
| Rung 4 | `Calculus.Spine` plus instance spines: exact dependent refusal-packet preservation |
| Rung 5 | `Calculus.Comparison`: closed indexed comparison laws and dependent receipts |
| Rung 6 | `Calculus.Crossing` plus Weathering/bounded-paid inhabitant: decide once, store both native outcomes, project downstream |
| Rung 7 | `Calculus.Instances.BreakGlass*`: origin/history-bound lifecycle, audit, spine, comparison, and stored crossing |

The root proves none of its own runtime adoption. A runtime claiming this
surface must map every in-scope governed distinction and show that each
survives implementation and transport; the full obligation is in
[`../../WHAT-THIS-PROVES.md`](../../WHAT-THIS-PROVES.md#formal-contract-and-runtime-conformance).
Inventory and per-rung fences:
[`../../docs/V14-RELEASE-LEDGER.md`](../../docs/V14-RELEASE-LEDGER.md) and
[`../../docs/V14-READINESS-LEDGER.md`](../../docs/V14-READINESS-LEDGER.md).

## Historical changelog through v12

Custody labels and target names in this dated changelog describe the trees in
which those entries landed. They are not current classifications; see the v14
section and release ledger above for present paths and roles.

### 10.0.0 — deprecated compatibility shim retired (2026-07-14)

- Removed `LeanProofs/Admissibility/CalculusOne.lean` and the deprecated
  `Admissibility.CalculusOne.calculus_one_compiles` marker. The removal was
  originally scheduled for 2.0 but deferred through v9; v10 completes the
  breaking cleanup. Downstream code must import
  `LeanProofs.Admissibility.AdmissibilityKernels` and use
  `Admissibility.Kernels.kernels_compile`.
- Reconciled the live registry and build map after removal: 66 files total;
  38 imported by the root aggregate, three more covered only by default targets
  (two ANNEX plus `ConsequencePartition`), and 25 files covered by neither.

### Unreleased — formalization-leading specimen laws L3–L7 (2026-07-09, second pass)

- **Five further UNRATIFIED-CANDIDATE specimens**, same fence as `RRPProfileSpecimen` (unwired, build directly; formalization does not wait on runtime adoption, while promotion keeps its separate correspondence-evidence review). Formalization leads implementation: these are the laws the runtimes are SUPPOSED to satisfy, written first.
  - `StandingProfileSpecimen.lean` — active collector basis derives `actor_has_standing`; revoked basis, schedule, operator ack, and model output each refuse by theorem; the claim is (actor, project)-scoped, non-transferable at the effect gate.
  - `WLPAppendAckSpecimen.lean` — append acks / publication receipts are custody evidence, never claim authority: `transport_evidence_mints_no_claims`, `append_ack_supports_custody_but_not_authority`, `more_transport_evidence_never_authorizes` (volume is not conversion).
  - `BridgeCustomsSpecimen.lean` — pairwise crossing only: `source_permit_alone_no_target_effect`, `bridge_claim_cannot_widen_scope` (the claim carries the cap), `target_profile_mismatch_no_local_claim`, `source_refusal_no_local_claim`. Verifier is a stipulated flag; no PKI, no registry, no transitive crossing.
  - `ActorTraceSpecimen.lean` — `actor_trace_hop_does_not_transfer_standing` absent an explicit directional transfer rule; `truncated_trace_no_reliance` (a partial trace is no evidence). Consumption-side twin of `DynamicTrace`'s production-side attribution; connecting them is a future promotion decision.
  - `LocalBoundaryPressure.lean` — concrete hostile instance for the merge seam: `WeakMergeAdmissible` (= `MergeAdmissible` minus `left_sound`) accepts a two-domain merge that leaks in one step (`weak_merge_is_not_merge`); discharges the inhabitation debt of `LocalBoundary`'s parametric pressure tests and names the load-bearing field by construction. No edits to the green ANNEX aperture.
  - `ScopedCertification.lean` — the *quis custodiet* seam: certification force is claim-class × scope confined (`certification_class_confinement`, `certification_scope_confinement`); delegation does not compose for free (`certification_not_transitive_without_rule`; one-hop-from-direct-donor by construction); self-claims mint nothing (`self_certification_does_not_establish_authority`); revocation and challenge are separate axes, proved by inhabited separation witnesses (`challenge_is_not_revocation`, `revocation_is_not_challenge`), with filed ≠ admitted (`filed_challenge_alone_does_not_block_reliance`). Universal authority is unrepresentable — a documented fence, not a marker theorem. The bootstrap ("this profile is rightly active here") is explicitly NOT formalized.
  - `SpendabilitySpecimen.lean` — the LA seam's anti-free-conversion laws: eligibility is contractible and required but never payment (`eligibility_does_not_mint_capacity`, `duplicated_eligibility_buys_nothing`); capacity is linear (`replay_refused`, inductive `wf_conserves` — conserved ≠ safe); deposits must cite admission; fork residue: revocation blocks the future and provably cannot reach the effect log or refund counts (`revoked_fork_blocks_future_spend`, `revocation_does_not_unwind_effects`, `residue_not_erased`). NOT LA's own Lean twin; proves nothing about it.
  - `CustodyFreshnessSpecimen.lean` — fresh-here ≠ fresh-there: freshness is evaluated against the producer clock only (`custody_time_does_not_launder_observation_time`, `hop_does_not_refresh`, `absent_producer_clock_never_fresh`); the tempting "recently checked somewhere" evaluator is modeled and refuted by two inhabited separation witnesses rather than merely omitted.
  - `TemporalBasis.lean` — time assurance for the NQ seam (NQ-T4, written before NQ implements its temporal track): *freshness is admitted elapsed time under a declared witness contract*. `fresh_requires` inversion + per-surface refusals (undeclared window, missing authority time, unadmitted clock, oversized uncertainty, stale); minted ≠ observed (`generated_at_does_not_refresh_observation`, tempting `freshByGeneration` refuted); elapsed ≠ revived (`retired_source_cannot_become_live_by_time_passing`); silence ≠ recovery (`silence_does_not_establish_clear`); existed ≠ fresh; late ≠ timely (`late_success_is_not_timely_success`); two clocks ≠ an order (`cross_basis_ordering_not_established`). No `GlobalTrustedTime` — every verdict Profile-indexed.
- **CI widened to the release envelope**: explicit `lake build LeanProofs AdmissibilityMathlibIslands` step plus the five repo audit scripts, so "CI green" again means "release claim green" after the 2026-07-08 default-target split.

### Unreleased — RRP profile specimen + DeferredWitness reflection (2026-07-09)

- **New UNRATIFIED-CANDIDATE:** `RRPProfileSpecimen.lean` — minimal profile-checker semantics for the RRP admissibility-gate prototype (runtime correspondence target: `~/git/rrp`). Finite symbolic model: `Receipt`/`Claim`/`ClaimRule`/`EffectRule`/`Profile`, `deriveClaims`, `decision`. Theorems: `missing_receipt_no_claim` (+ kind form), `cannot_testify_no_claim`, `stale_receipt_no_claim`, `revoked_basis_no_claim`, `effect_requires_claim`, `no_required_claim_no_permit`, `no_evidence_no_permit`, `profile_id_only_no_decision`, `digest_mismatch_refused`, `self_authorization_refused`. No JSON, no SHA, no parser, no transport; decision-level obstruction payloads deliberately coarser than the RRP ABI (receipt-level codes are refusal theorems here, not payloads). Unwired; build directly with `lake build LeanProofs.Admissibility.RRPProfileSpecimen`. Formalization does not wait on RRP. Under the current custody fence, ANNEX promotion still requires RRP to identify the named theorems it adopts; that citation is not by itself proof of runtime conformance.
- **DeferredWitness reflection lemma proved:** `firstViolation_none_iff_lawful` — the executable classifier agrees exactly with `LawfulCompletion` (previously documented as "left to the host environment"). Corollary `firstViolation_isSome_iff_not_lawful`. Custody unchanged (ANNEX); `Backflow` order and `#eval` examples preserved.
- `scripts/check-mathlib-free-targets.sh`, promised by the 2026-07-08 entry below, is delivered in this pass: it walks the static import closure of `AdmissibilityCustodyAnnex` (from `lakefile.toml` roots) and fails closed on Mathlib imports or heavy-island roots.

### Unreleased - Mathlib import-surface split (2026-07-08)

- `AdmissibilityCustodyAnnex` is the cheap Mathlib-free custody target: public kernels plus the ANNEX modules that do not import the cross-boundary/composition island.
- `AdmissibilityMathlibIslands` names the explicit heavy admissibility island: `CrossBoundaryExposure`, `CrossBoundaryDegradation`, `CrossBoundaryFailureMint`, `CrossBoundaryCascade`, `Composition`, and `LocalBoundary`.
- Default `lake build` no longer names the root `LeanProofs` aggregate. Build the full aggregate explicitly with `lake build LeanProofs`; it reaches Mathlib through `Paper24SharedVision`, `Paper25EpistemicBorderControl`, and the Finset-backed cross-boundary modules.
- `scripts/check-mathlib-free-targets.sh` guards the cheap custody target and fails if it imports Mathlib or the known heavy roots.

### Unreleased — DeferredWitness promoted SCRATCH → ANNEX (2026-06-26)

- `LeanProofs/Scratch/DeferredWitness.lean` → `LeanProofs/Admissibility/DeferredWitness.lean`. Namespace `DeferredWitness` → `Admissibility.DeferredWitness`; `Custody-Class: ANNEX` marker added; wired into `LeanProofs.lean` (refusal-kernel cluster). Sorry-free; outside the 1.0 compatibility claim. **Promotion context (then called a forcing context):** NQ's EVIDENCE_RETIREMENT basis-stale slice needed to cite the kernel as *evidence* under the `[annex]` pinning discipline (`nq` repo, `docs/theory/ROADMAP_EXPECTATIONS_FROM_LEAN_KERNEL.md`) rather than steer implementation from a `[scratch]` module, which that discipline forbids. This was promotion evidence, not permission to formalize.
- **Registry-count drift flagged (NOT reconciled in this pass).** `scripts/check-custody-classes.sh` now reports **55 files** — PUBLIC-SHIPPED 9, ANNEX 27, UNRATIFIED-CANDIDATE 16, SCRATCH 2, DEPRECATED 1. The prose counts throughout this README ("47 `.lean` files", "ANNEX (27)", "UNRATIFIED-CANDIDATE (16)", "Thirty-nine of the 55 … wired") predate three earlier UNRATIFIED-CANDIDATE additions *plus* this promotion and are stale. Left for a dedicated count-reconciliation pass rather than guessed at here — only the marker, the wiring, and this receipt are claimed. *(Reconciled 2026-06-26 — see next entry.)*

### Unreleased — registry counts reconciled (2026-06-26)

- Prose counts throughout this README brought into agreement with `scripts/check-custody-classes.sh` (55 files: PUBLIC-SHIPPED 9, ANNEX 27, UNRATIFIED-CANDIDATE 16, SCRATCH 2, DEPRECATED 1) and with the `LeanProofs.lean` import graph (39 wired = 9 + 27 + 1 + 2 root-imported candidates; 16 fenced = 14 remaining candidates + 2 scratch). Touched: the five-class summary, the ANNEX 14/11 sub-split, the kernel-adjacent table (`DeferredWitness` row added), the fenced-material list (added `CarryLaws`, `NoFreeLift`, `NoFreeStandingBridge` — the three UNRATIFIED-CANDIDATE modules added before this pass), and the two wired-count sentences.
- **Audit, not guess.** Counts were derived from a per-file `Custody-Class:` marker sweep and verified against `LeanProofs.lean` imports, not inferred from the old prose. The DeferredWitness annex split is kernel-adjacent (refusal kernel), so 14→16 kernel-adjacent and consumer specimens unchanged at 11.
- **One count deliberately left stale:** the "Refusal kernel taxonomy" section still reads *four* refusal kernels. Folding `DeferredWitness` into the existential-vs-conditional split is a content judgment about its theorem shape, not a registry count, and carries an in-place flag instead.

### Unreleased — custody discipline

Infrastructure:
- Per-file `Custody-Class:` markers across all `.lean` files in `LeanProofs/Admissibility/` (the gate enforces one per file regardless of count), drawn from the five ratified classes (`PUBLIC-SHIPPED`, `ANNEX`, `SCRATCH`, `UNRATIFIED-CANDIDATE`, `DEPRECATED`). Class vocabulary ratified in the papers repo at `working/custody-classes.md`.
- New `scripts/check-custody-classes.sh` — regression-checks marker presence and class validity; exits non-zero on missing or unratified markers.
- `ANNEX` ratified as the fifth custody class: compiled supporting material, scope-declared and regression-covered, but not promoted as public kernel authority.
- `AdmissibilityKernels.lean` scope-fence extended to enumerate 11 internal consumer specimens previously unclassified at the aggregator level (`AttestationLedger`, `AuthorizedNotSafe(Witness)`, `AuthorizedStepNotSafe(Witness)`, `SafetyBridge(Witness)`, `SafetyTrajectory`, `ConsolidationDenial`, `RefusalPropagation`, `Examples`). Annex now declared in two sub-groups: kernel-adjacent (13) and consumer specimens (11).
- `Custody:` prose paragraphs added to the 7 PUBLIC-SHIPPED layer kernels + the aggregator that previously lacked them; only `Freshness` carried prose before this pass.

No public surface change. No theorem content change. The 8 PUBLIC-SHIPPED module signatures are unchanged.

### 1.1.0 — 2026-06-03 (minor)

Rename:
- `LeanProofs/Admissibility/CalculusOne.lean` → `LeanProofs/Admissibility/AdmissibilityKernels.lean`. The aggregator's public claim moves from "Admissibility Calculus 1.0" to "Admissibility Kernels 1.0". Doctrine, not refactor: "calculus" overclaimed the artifact shape; the word is now reserved for the unified object this stack refuses to be.
- Namespace `Admissibility.CalculusOne` → `Admissibility.Kernels`.
- Marker theorem `calculus_one_compiles` → `kernels_compile`.

Compatibility:
- `CalculusOne.lean` retained as a one-line re-export shim under the old namespace for one minor version; carries `Custody-Class: DEPRECATED` and is scheduled for 2.0 removal.

No public-surface change. No theorem content change. The 8 PUBLIC-SHIPPED module signatures are unchanged.

### 1.0.1 — 2026-05-24 (patch)

Fixes:
- Repair `CrossBoundaryCascade` parse error (`Step.exposeFromExposure` constructor body: multi-line `insert (...)` inside a structure update required parentheses to terminate cleanly).

Infrastructure:
- Wire all Admissibility modules into `LeanProofs.lean` (full set: twenty-three modules including the previously-unwired four `CrossBoundary*` specimens and the two experimental `Composition` / `LocalBoundary` modules).
- `lake build` (no args) now covers the full stack, preventing silent unwired-module failures.

No public surface change. No slogan change. The 1.0 aggregator (then named `CalculusOne.lean`; now `AdmissibilityKernels.lean`) remains the public surface.

> 1.0.1 strengthens regression coverage without changing the 1.0 public surface.

### 1.0 — 2026-05-24

Initial named public surface. Eight modules in the 1.0 aggregator (originally named `CalculusOne.lean`; renamed 2026-06-03 to `AdmissibilityKernels.lean`): `Authority`, `StateTransition`, `Derivation`, `Execution`, `Corrective`, `Freshness`, `SurfaceAuthorization`, `WitnessInvariance`. Seven specimen consumers in `Examples.lean`. Slogan, scope-fence, and annex documented in this README.

## Historical roadmap through v13, with v14 closeout

This pre-v14 roadmap is retained as decision history, not the current release
queue. Its recorded split between local kernel families remains useful, while
the later v14 campaign earned a different bounded compositional object.

- **v14** — all seven rungs admitted; the separate capital-C naming act was
  ratified and `v14.0.0` released. See the current-surface section above.

- **v13** — released custody/path correction only. The skunkworks transfer,
  fail-closed registries, and integrated verification are complete; no new
  mathematical campaign was added.
- **Public evidence** — new finished countermodels or specimens may return
  from skunkworks without entering `AdmissibilityKernels`; an evidence target
  is a legitimate terminal home.
- *(optional)* `RefusalKernels.lean` — a possible future exact stable root over
  selected generic refusal laws.  It is not part of the 1.0 aggregator and is
  not earned by accumulating specimens.
- **2.0** — two candidate axes for future kernel families. Neither is a step toward a unified calculus; both are separate kernel families whose promotion would land independently:
  - *Composition axis* — refusal-propagation kernels. Promotion requires at least one theorem of the shape *if A cannot witness B and B is required as basis for C, then A cannot witness C for binding use*. Not earned by additional specimens alone.
  - *Safety axis* — value-preservation discipline over authorized transitions, where `Allowed` is authorization and `bridge` is a separate preservation witness. Skeleton present in the safety-bridge family (`SafetyBridge`, `SafetyTrajectory`, `AttestationLedger`). The safety-axis publication path is a standalone formal-methods preprint, not a unified-calculus rename.

> **Specimens mature in skunkworks and may return as public evidence.
> Composition rules would require a separate kernel family, not a
> unified-calculus rename.**

> **A refusal kernel blocks one laundering move. A propagation kernel would explain how blocked moves compose. Neither is a unified calculus.**

> **Pipeline composition is not refusal-propagation composition.** Pipeline composition connects predicates across a representation boundary via data-flow; the composition-axis criterion above is theorem-level transitivity over blocked witness promotions (`A ⇏ B; B basis for C; ∴ A ⇏ C`). The two are distinct, and pipeline composition does not satisfy the propagation-axis criterion.

## Admissibility Kernels 1.0 — public surface

A Lean authority kernel with typed verdicts and object-level refusal theorems
for admissible transition. General composition rules and meta-theorems are out
of scope for 1.0 and remain separate kernel families; pipeline wiring is not a
free composition theorem. Not a sequent calculus, process calculus,
proof-theoretic admissibility logic, or unified maximal calculus — see the
scope fence below.

`AdmissibilityKernels.lean` is the named public aggregator. Importing it brings the 1.0 surface into scope. Eight modules are tagged `[1.0]` and form the compatibility claim:

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

> Admissibility Kernels 1.0 models when evidence-backed claims may authorize transitions, proves that boundary-crossing upgrades are impossible by construction, and refuses laundering across the surface, freshness, witness, and authority axes.

Seven specimen consumers live in `Examples.lean` (imports `AdmissibilityKernels`): valid advisory result, valid authorized mutation, stale evidence refusal, self-cert denial, conflicting precedence denial, receipt-without-authority non-upgrade, open finding accounted.

## Scope fence — what 1.0 does NOT claim

1. 1.0 does not prove a general theory of institutions.
2. 1.0 does not claim recovery doctrine. `PublicReceiptRefinement` and
   `RecoveryMargin` are public evidence outside the root.
3. 1.0 does not claim cross-boundary process composition. The
   `CrossBoundary*` family is public Mathlib evidence.
4. 1.0 does not claim numerical-kind or artifact-kind axes.
   `NumericalAdmissibility`, `FiatAdmissibility`, and `AxisSkew` are public
   evidence.
5. 1.0 does not claim a calculus of communicating processes. `Composition` is
   diagnostic public evidence; `LocalBoundary` now lives in skunkworks.
6. 1.0 does not claim formal verification of any real-world institution,
   system, or paper. Root-level paper consumers and internal specimens remain
   outside the exact eight-module closure, whether public evidence or
   skunkworks incubation.

## Public evidence and separate stable siblings

The following finished modules remain public without entering the 1.0 stable
root. `DynamicTrace`/`FreshnessDynamicTrace`, `SafetyBridge`, PathVerdict, and
the v14 Admissibility Calculus have their own exact roots; concrete wounds and
witnesses remain public evidence where the registered closures exclude them.

### Kernel-adjacent public material

| Module                       | Role                                                      |
| ---------------------------- | --------------------------------------------------------- |
| `CorrectiveBoundary`         | Model-dependence boundary result (parallel mini-kernel)   |
| `PublicReceiptRefinement`    | Recovery doctrine companion to `SurfaceAuthorization`     |
| `RecoveryMargin`             | Visible-vs-capacity gap refusal (within-interval)         |
| `ClosureEligibility`         | Survival-vs-closure refusal (end-of-interval)             |
| `DeferredWitness`            | Pending/lapsed-vs-admissible refusal (deferred witness)   |
| `FiatAdmissibility`          | Artifact-kind × use-kind axis                             |
| `NumericalAdmissibility`     | Numerical-kind × use-kind axis                            |
| `AxisSkew`                   | Directional comparison axis (lagging/matched/leading)     |
| `PredicateWitnessSeparation` | Predicate satisfaction vs admissibility-witness wall        |
| `AuthorityScope`             | Scoped conversion receipt / no-universal-key specimen      |
| `DynamicTrace`               | State-threaded trace calculus over authorized static steps  |
| `CrossBoundaryExposure`      | Cross-boundary exposure mint specimen                     |
| `CrossBoundaryDegradation`   | Cross-boundary degradation provenance specimen            |
| `CrossBoundaryFailureMint`   | Cross-boundary failure-to-exposure mint specimen          |
| `CrossBoundaryCascade`       | Cross-boundary cascade reachability specimen              |
| `Composition` `[experimental]` | Diagnostic: process syntax alone does not make a calculus |
| `LocalBoundary` `[skunkworks]` | Experimental aperture toward a propagation/composition kernel |

### Public consumer specimens

Exercise the public surface in concrete settings. The SafetyBridge /
AuthorizedStep families instantiate the typed-verdict and execution kernels
against safety-trajectory specimens; `ConsolidationDenial`, `Examples`, and
`AttestationLedger` are illustrative. `RefusalPropagation` moved to
skunkworks because its generic law is mixed with tool-named fixtures.

| Module                       | Role                                                      |
| ---------------------------- | --------------------------------------------------------- |
| `AuthorizedNotSafe`          | Frontier 1 single-step wound (StepAllowed layer, axiomatic) |
| `AuthorizedNotSafeWitness`   | Frontier 1 wound consistency discharge (concrete parallel) |
| `SafetyBridge`               | Abstract bridge primitive + `SafeStep` gate (actor-inert) |
| `SafetyBridgeWitness`        | Non-contamination bridge specimen + boundary separation   |
| `AuthorizedStepNotSafe`      | Frontier 1 wound at verdict layer (kernel-legible all-green) |
| `AuthorizedStepNotSafeWitness` | Verdict-layer wound discharge + `SafeAuthorizedStepC` gate |
| `SafetyTrajectory`           | Trajectory pair + forgetful map + no-lift theorem         |
| `AttestationLedger`          | Tier-1 second concrete witness (Nat-textured, 2 actors)   |
| `ConsolidationDenial`        | Fluency-vs-settlement gap refusal (between-interval)      |
| `RefusalPropagation` `[skunkworks]` | Mixed generic/tool-named refusal-propagation specimen |
| `Examples`                   | Seven public-surface specimen consumers                   |

### Skunkworks-bound Admissibility work

All Admissibility incubations have moved to skunkworks. `Conductance`,
`Mandamus`, `ParameterizedMerge`, and the P27 skeleton live under
`formalization/Calculi/Scratch/`; `RefusalPropagation` has its sibling campaign
there. `LocalBoundary` and `LocalBoundaryPressure` live in the explicit
non-default `formalization/MathlibIncubation/` island. Their public originals
are deleted.

`BoundaryWitness`, `GuardCollapse`, `CarryLaws`, and `NoFreeLift` were
superseded and are absent from the v13 release tree; Git/v12 preserves their
history.

The former candidate specimens not listed above have been adjudicated as
terminal public evidence. Runtime citation/adoption identifies an intended
contract. A conformance claim still requires an explicit scope and
exact correspondence map, executable preservation and transport evidence, and
revision-bound qualification receipts. A formal refinement proof may
strengthen covered obligations but does not waive those artifacts.

### Refusal kernel taxonomy

The public evidence contains several refusal kernels, each proving a scoped
`surface ⇏ substance` non-implication, with distinct theorem shapes:

- **Existential-countermodel kernels** (3): `RecoveryMargin`, `ClosureEligibility`, `ConsolidationDenial`. Each exhibits one concrete state where the surface predicate holds and the substantive predicate fails. The theorem is `∃ s, Surface s ∧ ¬ Substance s`. One-shot refusal. Sufficient to break the inference *Surface ⇒ Substance*.
- **Conditional-rule kernel** (1): `SurfaceAuthorization`. Universal over action kinds and surface statuses: if cause-specific action AND collapsed surface AND no breakers, then deny. The theorem quantifies over inputs and returns a verdict, with companion theorems filling out the verdict space. Not a one-shot countermodel; a parameterized refusal rule.

Both shapes inhabit the same operator family (catalog at `~/git/papers/working/tooltheory/refusal-kernel-to-refusal-receipt-seam.md`). The shape difference matters for how the kernel composes (or refuses to compose) with future propagation-axis candidates — see Roadmap above.

> **[taxonomy correction, verified 2026-06-26; recorded in current custody
> 2026-07-16]** `DeferredWitness` is a refusal kernel, but **not** an
> existential-countermodel one. Its load-bearing content is
> `LawfulCompletion` (a universal conjunctive admissibility rule) plus an
> executable `firstViolation` classifier with the soundness biconditional
> `firstViolation u = none ↔ LawfulCompletion u` and a temporal lifecycle.
> The honest catalog is **five kernels, three shapes**: three existential
> countermodels, the conditional `SurfaceAuthorization` rule, and the
> `DeferredWitness` lifecycle classifier.

## Modules

### Layer 0 — `Authority.lean` `[1.0]`

Verdict algebra: `authorityVerdict : Basis × Precedence × Standing → AuthorityVerdict`. **Authorized iff all three dimensions green.** Pure — no stores, no actors, no mutation. Direct parameters (no half-evaluated `Transition` struct).

### Layers 3a + 3b — `StateTransition.lean` `[1.0]`

Governance state partitioned into four orthogonal stores (`PolicyStore`, `EvidenceStore`, `GapStore`, `RevocationStore`). `Step` inductive with one constructor per mutation kind; `applyStep` mutates exactly one store per Step.

**Trapdoor invariant: only `Step.amendPolicy` can touch `PolicyStore`.** Layer 3b adds `StepAllowed` (per-step standing predicate gating raw mutation) and the `executeIfAllowed` wrapper. Even authorized non-amendment cannot mutate `PolicyStore`.

### Layer 2 — `Derivation.lean` `[1.0]`

Read-side bridge from `GovState × Actor × AuthorityClaim` to component verdicts. Bundled-structure design: `BasisDerivation` etc. carry both the function (`deriveBasis`) **and** its proof obligations (`revoked_never_admissible`, `revoked_standing_never_standing`) — concrete implementations must discharge spec at construction. Basis and standing revocation consequences (`revoked_basis_never_authorized`, `revoked_standing_never_authorized`).

### Layer 4 — `Execution.lean` `[1.0]`

Combines mutation standing (`StepAllowed`) with claim authorization (`decideAuthority`). `AuthorizedStep env state actor` is a structure that bundles a `Step` with *both* permission proofs by construction — no half.

**Load-bearing theorems:** `revoked_basis_cannot_be_authorized_step` and `revoked_standing_cannot_be_authorized_step` — if a claim's basis or invocation standing is revoked, no `AuthorizedStep` for that step can exist. Plus four lifted store-isolation theorems through `executeAuthorizedStep`.

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

### Sibling — `CorrectiveBoundary.lean` `[public evidence]` (added 2026-05-07)

**Boundary-result module.** Not part of the five-module kernel proper; constructs a parallel miniature kernel with concrete payload types (`PolicyStore := List Nat`, etc.) and parameterized store ops, and proves model-dependence of the recorded null `corrective_then_forward_is_not_monotone`.

The previous `sorry`-bearing investigative null in `Corrective.lean` has been removed; the theorem statement is preserved as a comment-shape pointing here.

Two namespaces inside this module exhibit the model-dependence:

- `Identity` — store ops are identity functions. Proves `corrective_then_forward_is_monotone_universally`: under any env, the corrective-then-forward existential is FALSE.
- `Witness` — nondegenerate ops + a verdict-sensitive `BasisDerivation` that reads `policyStore` and `revocationStore`. Proves `corrective_then_forward_is_not_monotone`: a concrete witness `(initialState, recordRevocation 999, amendPolicy 1)` makes `WeaklyLessPermissive` fail at claim `1`.

The abstract `NondegenerateStoreSemantics` structure packages the three commitments from `papers/working/nondegenerate-store-semantics.md` (nontrivial store effects, verdict-sensitive derivation, mixed-class witness), and `corrective_then_forward_is_not_monotone_of_nondegenerate` proves the existential follows from the structure. `witness_satisfies_nondegenerate` verifies the witness model satisfies the structure; `witness_corrective_then_forward_is_not_monotone_via_abstract` recovers the witness theorem from the abstract path as a regression check.

The abstract kernel itself remains consistent with both the existential and its negation — that is the doctrinally-correct stance. The boundary module exhibits both possible answers without forcing the abstract kernel to commit. CLAIM-REGISTER #14 records the boundary result; A1 (the formerly-admitted sorry) is resolved.

### Sibling — `FiatAdmissibility.lean` `[public evidence]` (added 2026-05-11)

**Third admissibility axis: artifact-kind × use-kind.** Distinct from the authority-basis × state-mutation axis (`Authority` + `StateTransition`) and the witness × invariance axis (`WitnessInvariance`). Total `classify : ArtifactKind → UseKind → Classification`; every (kind, use) pair receives an explicit verdict (`allowed`, `requiresMediation`, `denied`, or `outOfScope`). The `outOfScope` verdict makes the kernel's silence audible — cases the kernel does not pretend to govern do not silently default. Closure property: no orphan corridors through which an artifact can claim a license it does not earn.

Keeper: *The admissibility kernel is itself admissible only under custody.*

Governs the relation between artifact kinds (axiom, definition, theorem, heuristic, metaphor, prestige token, proxy metric) and use kinds (orient, suggest, citeOrient, citeSupport, derive, authorize, mutateState, measureMagnitude). State mutation is the domain of the sibling `StateTransition` kernel; `FiatAdmissibility` does not pretend to govern it. Composition lemmas with the other admissibility kernels are explicitly deferred.

### Sibling — `NumericalAdmissibility.lean` `[public evidence]` (added 2026-05-12)

**Numerical-kind axis sibling to `FiatAdmissibility`.** Prevents one numerical kind from being treated as another: a score (constructed scalar with no native units) read as a quantity (measured magnitude); a rank (ordinal with no metric structure) read as value; a confidence (model's report about its own uncertainty) read as truth. Total `classify : NumericalKind → NumericalUse → Classification`; same closure-property shape as `FiatAdmissibility`.

Keeper: *A number's shape on the page does not license what the number can be asked to do.*

Sharper: *Score cannot imply magnitude; confidence cannot imply truth.* Rank, confidence, and probability cannot imply substrate at all; score, quantity, and proportion can reach substrate only through explicit mediation (calibration chain, measurement custody, population structure). Value claims always require utility structure for any non-quantity kind. Selection-by-extreme is never benign at the kernel layer. Several cells that look like keeper denials are mediation cells in disguise — value claims from any non-quantity kind require utility structure, so they discharge as `requiresMediation`, not `denied`.

### Sibling — `SurfaceAuthorization.lean` `[1.0]` (added 2026-05-11)

**Governor-facing refusal gate.** Sibling to the root-level `LeanProofs/CollapsedSurface.lean` (the discrete-finite negative kernel proving a collapsed surface cannot identify cause). This module adds the *authorization* consequence: a collapsed surface cannot authorize cause-specific consequence without discriminating evidence.

Keeper: *A collapsed surface may authorize inquiry. It may not authorize attribution.*

Governor-shaped form: *Cause-specific authority requires discriminating evidence.* Encodes the refusal gate (collapsed + cause-specific + no discriminator ⇒ deny). Does not encode the recovery machinery itself — `Breaker` is an abstract enum naming the three known recovery paths (preserved history, independent measurement, admissible perturbation); the predicates that constitute each kind remain unformalized here. Recovery doctrine lives in the sibling `PublicReceiptRefinement.lean`.

### Sibling — `PublicReceiptRefinement.lean` `[public evidence]` (added 2026-05-12)

**Recovery doctrine companion to `SurfaceAuthorization`.** Formalizes the simplest recovery channel: a public receipt refines an observation when it both excludes some cause the surface alone would admit *and* remains consistent with at least one surface-admitted cause.

Keeper: *Refinement narrows the admissible-cause set without collapsing it to empty.*

A receipt that excludes every cause is contradiction, not refinement. A receipt that excludes nothing is decoration, not refinement. Honest refinement lives between these two failure modes. Refinement does not, in general, identify a unique cause — narrowing is not identification. Abstract over receipt type and admittance predicate; concrete receipt schemas live in consuming systems (Governor's receipt schema, Paper 24's receipt-lineage discussion, NQ's witness intake). The other two recovery channels named in `SurfaceAuthorization`'s `Breaker` enum (independent measurement, admissible perturbation) remain abstract.

### Sibling — `ClosureEligibility.lean` `[public evidence]` (added 2026-05-12)

**Refusal kernel for closure verdicts on shift-bounded operations.** Invariant proved: `closure ⇔ (survived ∧ resolved ∧ slack-available)`. Any deficit on any of the three dimensions forces handoff or incident.

Keeper: *Survival is a handoff condition, not a closure condition.*

Sharper: *A survived shift with unresolved threat or depleted operator slack must emit handoff, not closure.* Same family resemblance as the admissibility-decay candidates: a visible outcome is being asked to license a substantive claim it does not, by itself, support. Sibling to `RecoveryMargin` (which governs within-interval visible-vs-capacity; this module governs end-of-interval survival-vs-closure). Sibling to `SurfaceAuthorization` (both encode refusal gates over claims given insufficient discriminating evidence). Nightshift-style operational doctrines are the obvious downstream consumer.

### Sibling — `RecoveryMargin.lean` `[public evidence]` (added 2026-05-11)

**Refusal kernel for the gap between a visible liveness signal and underlying recovery capacity.** Proves `VisibleGreen` and `RecoveryMargin` are independent predicates — the visible surface cannot serve as a witness for capacity.

Keeper: *Visible green does not entail recovery margin.*

In tightly-coupled, high-cost-of-deviation environments, a system can maintain visible status by sacrificing recovery capacity, and the dashboard cannot report the second condition. Discrete observation-equivalence specimen at the dashboard layer (see `LeanProofs/CollapsedSurface.lean` for the general cause-from-render kernel and Paper 25 for the matrix/dynamical version). NQ-style witness-standing findings are the obvious downstream consumer (where the dashboard is being asked to testify about operability, not just status).

### Sibling — `ConsolidationDenial.lean` `[public evidence]` (added 2026-05-25)

**Refusal kernel for the gap between interaction fluency and audited settlement.** Proves that `Fluent` does not witness `SettlementAdequate` — a system whose output reads coherent may have zero completed settlement passes and a non-empty unsettled buffer. One-way non-implication only; the opposite direction (settlement without fluency) is not claimed.

Keeper: *Fluency is not a settlement receipt.*

Sharper: *Decay can clear the buffer without settling the debt. A decay-governed system can look stable by forgetting what it failed to learn. Audited discard is not rot — residue demoted under audit is a separate stock, not epistemic damage.* Same family resemblance as `RecoveryMargin` and `ClosureEligibility`: a visible surface signal is being asked to license a substantive claim it does not, by itself, support. Sibling to `RecoveryMargin` (within-interval visible-vs-capacity) and `ClosureEligibility` (end-of-interval survival-vs-closure); this module governs between-interval fluency-vs-settlement. Sibling to `Freshness` on the temporal axis — where `Freshness` governs metric-time admissibility of evidence (*is this timestamp within an acceptable window*), `ConsolidationDenial` names a phase-time refusal (*has any settlement interval occurred at all*).

The three-clock threat model (interaction λ_ext, settlement μ, decay δ) and the consolidation-interrupt controller (Schmitt-trigger safety invariant, four-stock dynamics B/K/X/R, mode-specific bounds) are *named* in the header as cybernetic provenance only; this module does not *model* them. Equations and a controller sketch live in the papers repo at `working/tooltheory/consolidation-denial.md` + `working/tooltheory/consolidation-denial-formal-sketch.md`. Nightshift, agent_gov, continuity, and NQ are the operational consumers.

### Sibling — `DeferredWitness.lean` `[public evidence]` (historically SCRATCH → ANNEX 2026-06-26)

**Refusal kernel for temporal backflow — the one lawful form of late-witness completion, and the laundering it is not.** Governs a claim asserted at t₁ and completed by evidence observed at t₂ > t₁ under a deferral grant. The discriminator lives entirely at assertion time: the grant must itself be witnessed *before* the claim relied on it (anti-necromancy), bound to the exact witnessed terms (no post-hoc widening), inside the window.

Keeper: *Signed is not witnessed; later evidence is not prior standing; a license to defer is itself a declared state requiring a witness.*

Distinct in shape from the existential-countermodel refusal kernels (`RecoveryMargin` / `ClosureEligibility` / `ConsolidationDenial`): in addition to the named contrapositives (`no_retroactive_standing`, `necromancy_rejected`, `mutated_terms_rejected`, `stale_evidence_rejected`) it carries an executable classifier (`firstViolation` over a disjoint, countable, never-graded `Backflow` taxonomy) and a lifecycle (`statusOf` → `refused` / `pending` / `completed` / `lapsed`, with `Admissible` gated to `completed` so a window closing with no completing witness *lapses* rather than drifting into de-facto admissibility). Layer B (budget/refresh — how many claims one grant may complete) is the declared open frontier. Operational consumer: NQ's EVIDENCE_RETIREMENT basis-stale slice (the `live → stale` evidence-currency transition); see the `nq` repo gap doc and the pinning-discipline memo `docs/theory/ROADMAP_EXPECTATIONS_FROM_LEAN_KERNEL.md`.

### Sibling — `Freshness.lean` `[1.0]` (added 2026-05-19)

**Metric-time admissibility axis.** Sibling to the kernel's existing ordinal-time apparatus (Step sequences, `WeaklyLessPermissive` preorder, `ClosureEligibility.NoRegress` pairs, `RevocationStore` evolution). Where the ordinal apparatus answers *"did this happen before that,"* `Freshness` answers *"is this timestamp within an acceptable window."*

Keeper: *Expired evidence cannot prove current standing. Future-issued evidence cannot prove current standing. Incoherent intervals cannot prove standing. Excessive clock divergence makes the assessment unsafe.*

Three positive predicates compose into `Fresh`: `TemporallyCoherent` (issued precedes expires), `DivergenceAcceptable` (verifier-issuer clock divergence within bound), `WithinValidity` (now falls inside skewed validity window). Five negative theorems mirror four of Standing's nine `AssessmentResult` verdict kinds: `expired_not_fresh` / `not_yet_valid_not_fresh` mirror `Expired` / `NotYetValid`; `incoherent_not_fresh` and `not_precedes_not_fresh` cover the two structurally-distinct failure modes of `TemporallyCoherent` under opaque `Time.le` (both map to `AssessmentCompromised`); `divergence_excessive_not_fresh` mirrors the other `AssessmentCompromised` branch. The fifth temporal verdict (`ReplayDetected`) stays in the kernel's ordinal apparatus.

Canonical correspondence target: `~/git/standing` (workload-identity / grant
authorization tool, production-quality Rust). The historical promotion review
identified `AssessmentResult::AssessmentCompromised` with this metric-time
"gap" seam. That is one scoped mapping observation, not a full runtime
conformance receipt; the runtime still owes an exact scope/map and
preservation/transport evidence.

Time is kept opaque (`axiom Time : Type` + four axiomatic operations: `le`, `add`, `sub`, `absSub`). Concretizing to `Nat`/`Int` would leak structural facts into theorems and break the abstraction over real consumer types (chrono's `DateTime<Utc>`). Composition with the other admissibility kernels is explicitly deferred — same defer-marker pattern as `FiatAdmissibility`. Not `Δt.lean`.

### Sibling — `CrossBoundaryExposure.lean` `[public Mathlib evidence]` (added 2026-05-21)

**Cross-boundary exposure mint specimen.** First brick in the cross-boundary artifact-specimen sub-family. Introduces a first-class `Exposure` artifact carrying `(origin, target, failure)` provenance and an operator-supplied `BoundaryPartition` (`Internal` / `External` Prop-valued predicates over abstract `Domain`). The only constructor that can add an exposure is `Step.expose`, and it requires `Boundary.authorized e.origin e.target = true`.

Keeper: *Boundary authorization is the exposure mint.*

Sharper: This is the exposure layer. Not damage. Not failure leakage. Not cascade. Not internal failure. Failure is not modeled here.

Theorem `no_external_exposure_without_authorized_edge` — under a boundary that authorizes no Internal→External edges, no reachable configuration can contain an exposure with Internal origin and External target. Proof technique is the same forward-closed-set invariant idiom used in `TaxonomyGraph` lane proofs; the novelty is the first-class artifact (`Exposure`) and the abstract boundary-partition layer, not the proof family. `Reach.trans` lives here as a utility lemma used by downstream sibling slices that project their reachability into this kernel.

Origin: outside-aperture audit (fresh-context model asked "is this a process calculus?") surfaced the candidate; inside-aperture kernel-overlap audit demoted/reparented the work from a proposed `Delta/` family into this `Admissibility/CrossBoundary*` sub-family. See `papers/working/cross-boundary-artifact-specimens.md` for the audit trail.

### Sibling — `CrossBoundaryDegradation.lean` `[public Mathlib evidence]` (added 2026-05-21)

**Cross-boundary degradation-provenance specimen.** Second brick. Extends the exposure kernel with a `degrade` action carrying a `Cause`: either `direct` (external trigger, no exposure precondition) or `fromExposure e` (which requires `e ∈ c.exposures ∧ e.target = d` as constructor arguments). Direct degradation is licensed; *exposure-attributed* degradation cannot fabricate provenance.

Keeper: *This is degradation provenance only. Not damage. Not failure leakage. Not cascade.*

Theorem `no_external_degradation_from_internal_exposure` — under a sealed boundary, no reachable configuration can take a `degrade_fromExposure` step on an External domain whose cited exposure has Internal origin. Direct corollary of `CrossBoundaryExposure.no_external_exposure_without_authorized_edge`, lifted through the projection pattern (richer `Config` with `grades : Domain → Grade`, `toExposureConfig` projection stripping the grade map, per-step projection lemma, `Reach.trans` chaining).

`Grade` is kept abstract; the provenance theorem is independent of grade semantics, so `initGrade : Grade` is an explicit parameter rather than an `Inhabited` instance. Grade-side dynamics (recovery, hysteresis, capability) belong on the persistence side, not in the `CrossBoundary*` family.

### Sibling — `CrossBoundaryFailureMint.lean` `[public Mathlib evidence]` (added 2026-05-21)

**Cross-boundary failure-to-exposure mint specimen.** Third brick. Introduces `FailureEvent (domain, failure)` as a first-class recorded artifact and a two-rule step relation: `fail d f` records a failure event with no boundary precondition (failure is a local-domain event), and `exposeFromFailure e` mints an exposure requiring *both* (a) `⟨e.origin, e.failure⟩ ∈ c.failures` (a recorded precedent) *and* (b) `B.authorized e.origin e.target = true` (boundary authorization).

Keeper: *Failure is not exposure. Failure can be recorded without crossing a boundary. Exposure from failure is minted only by boundary authorization.*

Two theorems:

- `no_exposeFromFailure_internal_to_external` (step-local) — a single `exposeFromFailure` step from an Internal origin to an External target is impossible under a sealed boundary. Direct from the constructor's authorization precondition; no `Reach` required.
- `no_external_exposure_from_internal_failure` (reachable-config) — no reachable configuration of the failure-mint system can contain an Internal-origin External-target exposure. Lifted via projection through the exposure kernel.

This is the rung that makes the English sentence presentable: *internal failure → recorded failure event → authorized exposure mint → (later) downstream consequence*. Each arrow is a constructor or theorem application; no prose glue.

### Sibling — `CrossBoundaryCascade.lean` `[public Mathlib evidence]` (added 2026-05-21)

**Cross-boundary cascade reachability specimen.** Fourth brick; the first *affirmative* theorem in the cross-boundary family. Introduces an abstract `AuthorizedPath (B : Boundary Domain) : Domain → Domain → Prop` inductive (two constructors: `edge` for single authorized hops, `cons` for chained ones) and a third step rule `Step.exposeFromExposure` that propagates an existing exposure to a fresh immediate-origin exposure across one authorized edge.

Keeper: *Cascade is authorized exposure reachability. Not inevitability. Not degradation. Not damage. Not recovery.*

**Immediate-origin discipline.** Each cascade hop mints `Exposure(d_prev, d_next, f)` whose `origin / target` are the *immediate* boundary crossing, not the ultimate failure source. This is what makes projection to the kernel clean — every minted exposure satisfies `B.authorized origin target = true` directly. If ultimate provenance is ever needed, a separate `CascadeChain` witness can be added later; do not overload `Exposure.origin` to mean both "immediate crossing origin" and "root cause."

Theorem `authorized_path_permits_endpoint_exposure` — given an `AuthorizedPath B d₀ dₙ` and a failure kind `f`, there *exists* a reachable cascade configuration containing some exposure to `dₙ` carrying failure `f`. Bootstrap: `Step.fail d₀ f` then `Step.exposeFromFailure ⟨d₀, d_first_hop, f⟩`, then chain `Step.exposeFromExposure` along the path. Existential, not inevitable; the theorem statement uses *permits* / *reachable* / *exists*, never *will* / *must* / *eventually*.

Composition with the rest: `step_to_exposure_reach` projects all three cascade actions to kernel reachability (`fail` → `Reach.refl`; both `expose*` rules → a single `Step.expose`). A local `Reach.trans` on cascade's own `Reach` chains the inductive-helper's bootstrap step with its IH-derived reach. No `CrossBoundaryDegradation` import — cascade is exposure propagation, not degradation.

Scope fence: no scheduling, no fairness, no rates, no `TaxonomyGraph`, no process syntax. *Topology, not selection.* If a future slice adds `EnabledStep` / `SchedulerAllows` / `ScheduledReach`, it lives in a separate `CrossBoundaryScheduling.lean`.

### Safety-bridge family — stable `SafetyBridge` + public evidence (added 2026-05-27 / 2026-05-28)

**Frontier-1 safety axis: addresses the Frontier 1 wound (Admissibility ≠ Safety) from the closed 2026-05-10 AGI-requirements reverse-gap audit (`historical/audits/AGI_REQUIREMENTS_REVERSE_GAP_AUDIT_2026-05-10.md`).** Eight modules organized as three bricks plus a second concrete witness. The receipt-side bricks (0–2) instantiate the abstract `SafetyBridge` over a Bool/poison receipt miniature; `AttestationLedger` is the second, textured (`Nat`-valued, ≥2 asymmetric actors) witness that the abstract layer is not receipt-specific. Companion documents in papers repo: `working/kernel-to-body-map.md`, `working/calculus-2-exit-criteria.md` (working note retains the historical "calculus" label), plus tier map and ρ-drop decision at `working/tooltheory/calculus-2-tier-map-2026-05-28.md` / `working/tooltheory/safety-bridge-rho-drop-decision-2026-05-28.md`.

Brick layout:

- **Brick 0 — single-step wound (StepAllowed layer).** `AuthorizedNotSafe` exhibits the wound axiomatically over the abstract surface. `AuthorizedNotSafeWitness` discharges its consistency caveat by constructing a parallel concrete miniature (evidence store as `List Receipt`, `appendEvidence` as cons), proving the three premise axioms are jointly consistent and the wound is not vacuous.

- **Brick 1a — verdict-layer wound.** `AuthorizedStepNotSafe` settles the deferred-transfer question from brick 0's scope clause: the full `Execution.AuthorizedStep` (both-proofs object carrying mutation standing AND a kernel-legible all-green verdict) also admits an unsafe witness. **Fence:** "all-green" here means kernel-legible all-green via a degenerate `fun _ _ => …` derivation env, NOT substantively-grounded legitimacy. The Loop-Capture / `L_t` mapping is a doctrinal reading outside this brick. `AuthorizedStepNotSafeWitness` discharges the caveat over a concrete `AuthorizedStepC` parallel miniature, computing the verdict via the real `Authority.authorityVerdict`.

- **Brick 1b — verdict-layer safety gate.** `SafeAuthorizedStepC` (in `AuthorizedStepNotSafeWitness`) bundles the actual `AuthorizedStepC` with the bridge witness; `.toSafeStep` adapter projects into the generic `SafetyBridge.SafeStep authEnv`. Canonical carrier preserves the authorization witness (not existentially erased) for downstream trajectory/custody work.

- **Brick 2 — trajectories.** The *generic* per-hop-actor inductives (`AuthorizedTraj E`, `BridgedTraj E`) and `bridgedTraj_preserves` over any `SafetyEnv E` live in `SafetyBridge.lean` after the 2026-05-30 canonicalization pass; both substrate (`SafeStep`) and witness-layer (`AuthorizedStepC`, `SafeAuthorizedStepC`) carry actor as a *field*, not a type parameter. The verdict-layer specialization in `SafetyTrajectory.lean` (`AuthorizedTrajC`, `BridgedTrajC`) carries the richer `SafeAuthorizedStepC` hop and provides the brick-2 specimens. Forgetful map `BridgedTrajC.toAuthorizedTrajC` makes the slogan "an authorized trajectory that does not lift to a bridged one" a *definition*, not rhetoric. Three theorems (verdict-layer):
  - `bridgedTrajC_preserves` — positive composition (bridged ⇒ floor preserved).
  - `authorized_trajectory_loses_value` — negative composition (authorized ⇏ floor preserved).
  - `no_bridgedTrajC_to_poison_end` — no-lift (the value-losing endpoint admits no bridged trajectory).

`SafetyBridge.lean` is the abstract primitive: `SafetyEnv (σ α ρ : Type)` with actor-inert `bridge : σ → α → Prop` and `preserves` obligation. Actor-inertness is a base design decision for the safety axis — `Allowed` keeps the actor, safety preservation is over the transition effect, actor-sensitive bridges are deferred to a named extension (`ActorSensitiveBridgeEnv` declared in the Open block, not implemented). If actor identity must change transition semantics, the right move is `run : σ → ρ → α → σ`, not smuggling `ρ` through `bridge`.

`SafetyBridgeWitness.lean` is the receipt-side non-contamination bridge specimen. Labeled "sufficient bridge specimen, not complete safety policy" — conservative structural bridges may reject value-preserving actions that pass a more discriminating policy. A maximal bridge collapses back into "bridge := preserves-restated"; the point of a structural bridge is checkability without first running the action.

`AttestationLedger.lean` is the tier-1 second concrete witness. Two-actor (writer/auditor) protocol with `Nat`-valued defended observable (`valid` standing attestations); three step types (`post`, `attest`, `revoke k`). The wound is an *authorized* revoke — actor-held legitimate standing destroying defended value, the sharper illustration of the L/V divergence shape than the receipt model gave. After the 2026-05-30 canonicalization, this file uses the substrate's generic `AuthorizedTraj ledgerEnv` and `BridgedTraj ledgerEnv` directly — `protocolHappyPath` (writer.post → auditor.attest) is one trajectory carrying two different per-hop actors, which is the acid test for the per-hop-actor substrate. Confirms the ρ-drop on non-degenerate evidence (the receipt model had `Actor := Unit`).

Keeper: *The lie is cheaper than the proof — authorization is a declaration (`= rfl`); preservation must be witnessed (`preserves` discharge).*

Candidacy note: this family is the safety-axis candidate, distinct from the Roadmap's composition axis (refusal-propagation theorems). The two axes are independent; neither is a step toward a unified calculus. The safety-axis publication path is a standalone formal-methods preprint. The composition axis and the self-amendment axis (Frontier 3) remain as separate kernel-family candidates with their own promotion criteria.

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

Audit provenance and a detailed walk-through live in `papers/working/cross-boundary-artifact-specimens.md`. The two-tracks rule (kernel-specimen track now; the unified-process-calculus / composition object was deferred for lack of an honest scoped statement and retired as a target on 2026-06-03) is filed in operator memory as `feedback-kernel-vs-process-calculus`.

## What the kernel warrants

> Governance-state mutation requires both mutation standing and an authorized claim verdict, and a revoked basis cannot produce an executable authorized step. Recovery-classified transitions cannot increase the authorized action set; authority-increasing recovery requires a separately classified forward transition with fresh basis.

## What it does NOT warrant

- Concrete `claimForStep` resolution. A runtime claiming this seam must map its
  resolver and discharge the abstract hypotheses.
- A concrete `AuthorityClaim` schema. Runtime representation belongs in the
  correspondence map.
- Behavioral laws on the abstract store API (`appendEvidence`, `applyUpdate`,
  etc.) — they are abstract symbols with no behavioral constraints. The
  structural partition invariant survives, but no concrete claim about what a
  receipt records follows without a runtime refinement.
- A bridge between `Derivation.deriveStanding` (standing to *invoke* a claim)
  and `StateTransition.*Standing` predicates (standing to *mutate* governance
  state). An end-to-end claim must supply or exclude that bridge explicitly.

## Build

The default build covers the Mathlib-free stable and public-evidence targets.
`AdmissibilityKernels`, `DynamicTrace`, `SafetyBridge`, `PathVerdict`, and
`AdmissibilityCalculus` are exact stable-family targets; `AdmissibilityEvidence` and
`PathVerdictEvidence` keep finished specimens outside those roots.
`AdmissibilityEvidenceMathlib` is the explicit heavy public-evidence island.
The root `LeanProofs` aggregate remains an explicit contact build, not a
promotion mechanism.

Public-surface gate: `lake build LeanProofs.Admissibility.AdmissibilityKernels` builds the aggregator; `lake build LeanProofs.Admissibility.Examples` exercises the specimen consumers through the public API.

No Lean proof holes as of 2026-05-28 in the wired stack. The word `sorry` does appear in docstring text within `Corrective.lean` and `CorrectiveBoundary.lean` as references to a resolved former-`sorry`; these are comments, not proof holes — a plain grep will find them.

### Historical cascade repair note

`CrossBoundaryCascade.lean` had a pre-existing parse error in its
`Step.exposeFromExposure` constructor. The two-character fix is now covered by
`AdmissibilityEvidenceMathlib` and the explicit `LeanProofs` contact build.

Representative narrow regression commands follow; target-level gates and the
whole-tree custody registry are the authoritative coverage checks.

```bash
# Target-level gates
lake build AdmissibilityKernels AdmissibilityEvidence
lake build DynamicTrace SafetyBridge PathVerdict PathVerdictEvidence
bash scripts/check-pathverdict-footprint.sh
lake build AdmissibilityCalculus
bash scripts/check-calculus-footprint.sh
bash scripts/check-mathlib-free-targets.sh
lake build AdmissibilityEvidenceMathlib
lake build LeanProofs

# Public 1.0 surface (aggregator + specimens)
lake build LeanProofs.Admissibility.AdmissibilityKernels
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

# Public evidence — axis & refusal kernels
lake build LeanProofs.Admissibility.CorrectiveBoundary
lake build LeanProofs.Admissibility.FiatAdmissibility
lake build LeanProofs.Admissibility.NumericalAdmissibility
lake build LeanProofs.Admissibility.PublicReceiptRefinement
lake build LeanProofs.Admissibility.ClosureEligibility
lake build LeanProofs.Admissibility.ConsolidationDenial
lake build LeanProofs.Admissibility.RecoveryMargin
lake build LeanProofs.Admissibility.AxisSkew
lake build LeanProofs.Admissibility.PredicateWitnessSeparation
lake build LeanProofs.Admissibility.AuthorityScope
lake build LeanProofs.Admissibility.DynamicTrace

# Public Mathlib evidence — cross-boundary artifact specimens
lake build LeanProofs.Admissibility.CrossBoundaryExposure
lake build LeanProofs.Admissibility.CrossBoundaryDegradation
lake build LeanProofs.Admissibility.CrossBoundaryFailureMint
lake build LeanProofs.Admissibility.CrossBoundaryCascade

# Safety-bridge stable core + public evidence
lake build LeanProofs.Admissibility.AuthorizedNotSafe
lake build LeanProofs.Admissibility.AuthorizedNotSafeWitness
lake build LeanProofs.Admissibility.SafetyBridge
lake build LeanProofs.Admissibility.SafetyBridgeWitness
lake build LeanProofs.Admissibility.AuthorizedStepNotSafe
lake build LeanProofs.Admissibility.AuthorizedStepNotSafeWitness
lake build LeanProofs.Admissibility.SafetyTrajectory
lake build LeanProofs.Admissibility.AttestationLedger

# Public diagnostic evidence
lake build LeanProofs.Admissibility.Composition
```
