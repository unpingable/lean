# Paper Map

Module → paper crosswalk. Inverse of the paper-side index in the papers repo at `docs/formalization-index.md`.

Companion documents:

- `WHAT-THIS-PROVES.md` — module-level exposition of what each layer proves and what it killed
- `CLAIM-REGISTER.md` — claim-level audit with BROKEN / STALE / SOUND / OPEN status for specific paper prose locations
- `NOTES.md` — architecture overview of the three-layer stack

This file exists so that a reader in the Lean repo can go the other direction: pick a module, find the paper(s) it cashes out into, and judge whether the mapping is clean enough to cite.

## Stable identifiers

- `P{N}` — preprint number (e.g., `P18`)
- See `../papers/preprint/` for the canonical paper directories

## Cashout classes

- **Certify** — Lean proves a claim the paper already makes
- **Sharpen** — Lean narrows, constrains, or corrects a prose claim
- **Expose looseness** — Lean shows the prose was doing multiple jobs in one sentence
- **Bridge artifact** — Lean creates a clean prose → formal statement → proof path

## Paper-ready vs formalized

A claim can be formalized without being paper-ready. This file flags mapping quality, not just theorem existence.

---

## `LeanProofs/TaxonomyGraph.lean`

Static pipeline graph over the 15-domain cybernetic failure taxonomy. 4 terminal domains, 3 terminal families, role coherence, reachability classification.

**Primary cashout:**

- **P15** (*Cybernetic Fault Domains*) — sharpen + expose looseness. The paper's taxonomy and fault-domain instantiations gain formal backing. Paper-ready. Kills "Δh is universal sink" as a reachability claim (see `CLAIM-REGISTER.md` #1).

**Secondary cashouts:**

- **P16** (*The Gain Geometry of Temporal Mismatch*) — certify. Therapeutic inversion count (13/15 domains; Δa and Δe lack one). Partial paper-ready.
- **P22** (*No Universal Plant Clock*) — resonance only. Three-terminal-families result is a structurally analogous "no universal X, multiple families" pattern, not a direct warrant for P22's specific claims. Noted in P22's README as resonance. (Earlier index drafts listed coupling-family isolation as a P22 tie-in; reclassified 2026-04-20 as too forced.)

## `LeanProofs/BranchSelector.lean`

Dual-budget model for closure-family selection. Budget asymmetry / priming / susceptibility. Kills "precursor type determines closure family."

**Primary cashout:**

- **P9** (*Capacity-Constrained Stability*) — certify + sharpen. Formalizes the mechanism behind "structurally predictable despite appearing sudden." Paper-ready. Relevant `CLAIM-REGISTER.md` entry: #10 (marked SOUND).

**Secondary cashouts:**

- **P18** (*Unauthorized Durability*) — sharpen. Context for which closure family dominates, feeding into the Δc→Δh persistence story.

## `LeanProofs/PersistenceModel.lean`

Five-state Δc→Δh dynamics. Cumulative rollback depletion under detached commits. External repair produces restructured, not aligned. Three-way recovery distinction. Quantitative burn + realization cluster (added 2026-05-08, three phases): `commit_burns_exactly` isolates the Nat-truncation boundary in the additive form `post.cap + burnRate = pre.cap` under `burnRate ≤ cap`; `commitsToHysteretic` provides the closed-form commit count to hysteretic (with cap=0 special case for the truncating-burn boundary); non-strict `commitsToHysteretic_monotone` and strict `commitsToHysteretic_strict_mono` (positivity-bounded) ground the "faster after repair" doctrine in `post_repair_faster_to_hysteretic`. Strict monotonicity requires both `0 < cap₂` and `cap₂ + burnRate ≤ cap₁` — the boundary case `cap₂ = 0, cap₁ = burnRate` is genuinely a tie (both burn out on first commit) and the `0 < cap₂` hypothesis excludes it cleanly. **Realization bridge** `commitsToHysteretic_realizes`: starting from a detached state (`detachedShort` or `detachedWarn`), replicating `commitsToHysteretic`-many `.commit` events lands in `hysteretic`. Two helpers (`step_commit_low_terminates`, `step_commit_high_continues`) plus strong induction on `rollbackCapacity` plus inline recurrence via `Nat.add_div_right`. Bridges closed-form commit-count arithmetic to actual `run`-trace semantics. Kills "prolonged contiguous detachment causes reset failure" and "repair restores baseline."

**Primary cashout:**

- **P18** (*Unauthorized Durability*) — sharpen + bridge. This module *is* the formalization of Paper 18's central mechanism. Paper-ready. Produces several novel claims not in Paper 18's prose (external repair → restructured; restructured systems fail faster; three-way recovery taxonomy). Acknowledged in P18 Appendix A (v1.1 candidate, drafted 2026-04-20, not yet pushed to Zenodo).

**Secondary cashouts:**

- **P22** (*No Universal Plant Clock*) — certify + bridge. The `persistence_normalizes` axiom explicitly marks the static/temporal boundary, aligning with Paper 22's scope-fence discipline. Acknowledged in P22 §6.4 as of pre-v1.0 incorporation (2026-04-20).
- **P8** (*Detecting Temporal Debt*) — sharpen, narrow. What "temporal debt" accumulates to: commitment, not elapsed time.
- **P19** (*Shadow Governance*) — certify (inherited from P18). No independent mapping; follows P18 revisions.
- **P6** (*Temporal Closure Requirements*) — expose looseness. SI-C "long enough" framing marked STALE in `CLAIM-REGISTER.md` #4.

## `LeanProofs/OpsMasking.lean`

Operational masking — case (i) projection clause. General lemma `trajectory_eq_of_projected_eq` (any two controllers whose gated actions agree pointwise produce identical trajectories under any plant dynamics and measurement map) plus paper-form corollary `projection_masking` ($\Pi(C+H) = \Pi(C)$ pointwise ⇒ outputs coincide exactly). Deterministic case only.

**Primary cashout:**

- **P23** (*Ops Is Control with a Non-Self-Identical Controller*) — bridge artifact + certify, case (i) only. Paper-ready for the kernel theorem; cases (ii) (measurement null-space, first-order) and (iii) (local gain aliasing, $\varepsilon$-resolution) remain paper-level only and are not yet Leaned. The kernel pins the signatures of "controller", "projection", "trajectory", and "observation" so the §3.3 prose claim survives translation.

**Signature note for future work:** the gate is currently a fixed function $\text{proj} : U \to U$ rather than the paper's authority-state-indexed $\Pi_{A_t}$. For case (i) this is harmless (the masking hypothesis is pointwise and absorbs gate-state dependence). Lifting to $\text{proj} : X \to U \to U$ is required if a future module wants to carry $A_t$ explicitly — e.g., to formalize the §2 continuity-budget inequality where authority delay is the load-bearing object. The §2 ADT bound is intentionally not Leaned.

## `LeanProofs/Paper24SharedVision.lean`

Algebraic shard for Paper 24's §4 metric probes and Theorems 3–4. Linear alias-break specialization $A_i(V) = V(1+\varphi_i)$, baseline-zero, pairwise-difference identity, two-agent absdiff and variance scaling, sup-norm-bound kernel for the witness filter, η-step bound, and the survivor-cohort centered-mean-zero algebra.

**Primary cashout:**

- **P24** (*Shared Vision as Coordinating Prior*) — sharpen + certify. Pins the §4 metric algebra and corrects a sign in Proposition 2: the formal pairwise difference is $(\varphi_i - \varphi_j)\cdot V$; the paper's proposition statement currently has the opposite sign. Metric claims (absolute value, square) are unaffected. Paper-ready for the algebraic core; intentionally does not formalize Conjecture 1, the agile case study, closed-loop dynamics, the witness-filter institutional prose, or the Big-O / noise-floor falsifiability hooks.

**Scope discipline.** The sup-norm bound is stated as hypotheses ($|\Phi(E^F)| \le \text{maxRetained} \le \tau$), not as an operator-theoretic abstraction over arbitrary aggregators. Lean's job here is to swat sign and scaling goblins, not to model governance.

## `LeanProofs/Paper25EpistemicBorderControl.lean`

**Status:** P25 formal spine sufficient — complete for structural-refusal claims; quantitative substitution scaling (Proposition 1) and closed-loop dynamics intentionally out of scope.

Algebraic shard for Paper 25's §5 sibling-vs-§N adjudication and §3.1 Theorem 1 epistemic-access core. Five theorems: row-replication operator (the operational form of $\mathbf{1}_N \otimes M$ for the homogeneous-witness case), kernel preservation under stacking, Gramian scaling identity, observation-equivalence implies policy-equivalence, and the target-distinct-but-policy-same corollary.

**Primary cashout:**

- **P25** (*Epistemic Border Control as Proxy Regulation Under Partial Observability*) — certify + bridge artifact + sharpen. Certifies §5's algebraic adjudication: homogeneous-witness aggregation preserves the observability kernel ($\ker(\mathbf{1}_N \otimes M) = \ker(M)$ for $N > 0$) and scales the Gramian by $N$ ($(\mathbf{1}_N \otimes M)^\top (\mathbf{1}_N \otimes M) = N \cdot M^\top M$), so Paper 24's clean aggregation cannot by itself solve Paper 25's substitution problem. Bridges §3.1 Theorem 1's prose by isolating the load-bearing structural refusal — observation-equivalent states get identical control sequences under any policy that depends only on observations — without dragging in the closed-loop induction the prose hand-waves (the closed-loop vindication is correct but separable from the structural refusal). Sharpens §5 via the explicit Gramian identity, which distinguishes subspace-preservation (always true) from individual-vector preservation (true only when the smallest singular value is non-degenerate). Acknowledged in P25 §5 as of v0.1 draft (clarifying paragraph + companion-repository pointer added 2026-05-03).

**Scope discipline.** The module deliberately does *not* formalize: the explicit finite-horizon observability matrix $O_T = [C; CA; \ldots; CA^{T-1}]$ as a single matrix object (the §5 corollary is mechanical once $O_T$ is in scope); closed-loop dynamics, Kalman filtering, or LQR (Theorem 1's closed-loop reading is an inductive vindication of a hand-wave, not the structural refusal); Proposition 1's quantitative Gramian scaling for the substitution magnitude (open in the paper); SVD or least-observable-direction quantitative claims (the kernel + Gramian results here are the qualitative substrate).

**Rhetorical note (intentional).** `target_distinct_policy_same` carries `_hTarget : target q x ≠ target q x'` as an intentionally-unused hypothesis. That is the structural content: the policy never sees the target, so target inequality cannot break policy equality. Sincere intent does not save the controller; observation geometry alone forecloses target regulation. The unused-hypothesis posture is the formal echo of the paper's Goodhart firewall.

## `LeanProofs/RepairOperator.lean`

Sovereign repair operator — hostile kernel check. Five-outcome classification, governed-cell partition, containment predicate (abstract), escalation operator with aging, two-tier terminal condition. Forces separation of structural invariants (provable) from political placeholders ($\sigma$, legitimacy) and measurement handwaving ($I(x)$, $O(G,t)$), which are left abstract.

**No current paper cashout.** Formalizes the working note `working/sovereign-repair-operator.md` in the papers repo. Sits outside the current 22-paper scope. Documented here to keep the mapping complete; not a current revision question.

## Companion simulations

The Lean repo also hosts two Python simulations co-located with the formalization work, referenced as companion artifacts by the relevant preprint READMEs:

- **`ops_continuity.py`** — Paper 23 companion. Instantiates the augmented state $\xi_t = (x_t, \hat{x}_t, c_t, \theta_t, A_t)$ with structured (biased/omissive) handoff loss, authority expansion after $\tau_{\text{auth}}$ delay, fatigue wear and fracture, and toggleable latent compensator $H_t$. Exhibits §4.5 Case A governance-induced ruin in phase sweep, case (i) projection masking bit-exactly, and case (ii) finite-horizon masking over a 4-step window.
- **`shared_vision.py`** — Paper 24 companion. Implements the §2 model and the §4 probes (aggregation-boundary, alias-compatibility, filter). Demonstrates Theorem 1 (mean-aggregation masking), supports Proposition 1 (no-scalar-free-lunch) across four canonical aggregator classes, exhibits Theorem 2 (alias-compatibility) under stationary $V$ vs strategic shift, and demonstrates Theorems 3 and 4 (witness-filter + temporal persistence) via the one-shot stack-rank probe.

Neither sim is a Lean module; both are referenced for completeness so the paper-side pointers in `papers/preprint/{23,24}-*/README.md` resolve to a single repo location.

## `BabyRiver/*.lean` (Phase 1 Baby River kernel)

State well-formedness preservation, action semantics (stay / consume / movement), Kaplan-Meier survival curve monotonicity, log-rank test bookkeeping. Scaffolding for Phase 2 population inference.

**No current paper cashout.** Sits outside the 22-paper scope. Candidate warrant for a future paper on biological/population-level Δt dynamics (not yet written). Documented here to keep the mapping complete; not a current revision question.

## `LeanProofs/Admissibility/` (Authority kernel — infrastructure substrate)

Five core modules forming a Governor-neutral authority kernel, plus two boundary-result siblings:

- `Authority.lean` — verdict algebra. `authorityVerdict : Basis × Precedence × Standing → AuthorityVerdict`. Authorized iff all three dimensions green.
- `StateTransition.lean` — partitioned governance state with isolation invariants. Only `Step.amendPolicy` mutates `PolicyStore`; `StepAllowed` gates raw mutation.
- `Derivation.lean` — read-side bridge from `GovState × Actor × AuthorityClaim` to component verdicts. Bundled-structure design (`BasisDerivation` etc. carry function + spec obligations). Revocation-shaped safety consequence.
- `Execution.lean` — `AuthorizedStep` bundles a step with both mutation standing (`StepAllowed`) and claim verdict (`authorityAuthorized`) by construction. Load-bearing theorem: revoked basis cannot produce an `AuthorizedStep`.
- `Corrective.lean` (added 2026-05-01) — corrective monotonicity layer. `classify : Step → StepClassification` (corrective / forward / neutral) is the enforcement surface; `WeaklyLessPermissive` is the preorder; `CorrectiveMonotone env` carries the proof obligation; `RecoveryEnv` bundles env + obligation and is the gate at which monotonicity becomes operationally required (recovery-facing APIs take `RecoveryEnv`, not raw `DerivationEnv`). Load-bearing corollary `corrective_no_authority_laundering` rules out same-basis laundering. The module's previously-admitted investigative null `corrective_then_forward_is_not_monotone` was replaced 2026-05-07 by a comment-shape pointing to the boundary module below; the kernel is sorry-free. Companion working note: `~/git/papers/working/admissible-recovery-semantics.md`.
- `CorrectiveBoundary.lean` (added 2026-05-07) — model-dependence boundary result. Builds a parallel miniature kernel with concrete payload types (`PolicyStore := List Nat`, etc.) and parameterized `StoreOps`, and proves the abstract kernel's recorded-null question is genuinely model-dependent: identity-store models make the corrective+forward existential FALSE; nondegenerate models make it TRUE. Abstract `NondegenerateStoreSemantics` structure packages the three commitments from `~/git/papers/working/nondegenerate-store-semantics.md`; `corrective_then_forward_is_not_monotone_of_nondegenerate` is the parametric theorem; `witness_satisfies_nondegenerate` certifies the witness model. The abstract kernel's existential remains formally undecidable in current vocabulary — that is the doctrinally-correct stance, and this module exhibits both possible answers without committing the abstract kernel to either.
- `WitnessInvariance.lean` (added 2026-05-08) — boundary primitive for witness-invariance failure. Formalizes the four-tier ladder (selectivity / specialization / encapsulation / modularity) from the multi-model 2026-05-08 distillation of McGee/Zhang/Blank 2026 (*Cognitive Science* 50(3)). Two namespaces: abstract `Encapsulated` / `MovesUnderExcludedPerturbation` definitions + boundary theorem `moves_implies_not_encapsulated`; toy counterexample (`ToyState` with `synBit`/`semBit` — `syntax` is reserved in Lean 4) proving `selectivity_does_not_imply_encapsulation`. Doctrine: prove the boundary claim, not the Wiley paper. Companion working note (papers repo): `~/git/papers/working/primitives/witness-invariance-failure.md`. Supplies missing invariance-discipline rung in the admissibility apparatus's witness-validation vocabulary; structurally adjacent to (but not directly equivalent to) P25 Theorem 1's projection-invariance shape.

**No paper cashout.** This is infrastructure substrate for a future Governor (`agent_gov`) implementation citation, not a paper-claim cashout. Concrete `claimForStep` resolvers and `AuthorityClaim` schema commitments belong in Governor's instantiation, not in the kernel. Documented here to keep the mapping complete.

Sibling to `LeanProofs/Admissibility.lean` (P27 obligation skeleton, namespace `P27`). Sorry-free as of 2026-05-07; three real proofs + two `True`-placeholder discharges pending sibling vocabulary; intentionally unwired (sorry-elimination does not imply wiring). The P27 skeleton and the Authority kernel are independent and address different layers (post-transition obligation accounting vs pre-action authorization). See `LeanProofs/Admissibility/README.md` for the six-module breakdown.

## `LeanProofs/Admissibility/` safety-bridge family (Frontier 1 — standalone preprint anchor)

Eight modules forming the safety-axis brick set, addressing the `FRONTIERS.md` Frontier 1 wound (`Admissibility ≠ Safety`) with a single-step wound + verdict-layer wound + trajectory triple + second concrete witness. Module-by-module description in `LeanProofs/Admissibility/README.md`; status (structurally addressed 2026-05-28) in `FRONTIERS.md`.

- `AuthorizedNotSafe.lean` / `AuthorizedNotSafeWitness.lean` (added 2026-05-27 / 2026-05-28) — Brick 0. The wound at the `StepAllowed` layer; axiomatic exhibition + concrete consistency discharge over a `List Receipt` parallel miniature.
- `SafetyBridge.lean` / `SafetyBridgeWitness.lean` (added 2026-05-28) — Abstract primitive: actor-inert `bridge : σ → α → Prop` with `preserves` obligation; non-contamination bridge specimen with structural discharge.
- `AuthorizedStepNotSafe.lean` / `AuthorizedStepNotSafeWitness.lean` (added 2026-05-28) — Brick 1a (verdict-layer wound transfer) + brick 1b (`SafeAuthorizedStepC` canonical-bundle gate with `.toSafeStep` adapter).
- `SafetyTrajectory.lean` (added 2026-05-28) — Brick 2. State-threaded inductive trajectory families with per-hop witnesses, forgetful map, and the trajectory triple (`bridgedTraj_preserves` positive; `authorized_trajectory_loses_value` negative; `no_bridgedTraj_to_poison_end` no-lift).
- `AttestationLedger.lean` (added 2026-05-28) — Tier-1 second concrete witness. Two-actor protocol, `Nat`-valued defended value, per-hop actor in trajectory type; the wound is an actor-authorized revoke (sharper L/V illustration than the receipt model).

**Primary cashout:**

- **Formal-methods preprint *"Safety-Bridge Kernel: Authorization and Value Preservation"* (subtitle: *Axis 1 of the Admissibility Suite*)** — bridge artifact + certify. Standalone preprint **outside the Δt Zenodo numbering** (target venue: Zenodo / arXiv-quality formal note). The Lean stack *is* the contribution; the preprint is exposition of finished work, not new construction. **Status: v0.2 draft; not yet published.** Title, abstract, claim list, and theorem-target table stable; suite-context framing reflects the 2026-06-03 cross-axis synthesis closure (synthesis closed *against* a single unifying calculus paper; surviving structure is the "disciplined premise production" umbrella with two named species — source/temporal and multiplicity/resource — plus a per-species architecture-gap audit). Working title earlier slugged as *"An Admissibility Calculus: Authorization, Safety Bridges, and Value Decay"*; that slug was demoted during drafting. Full topology and decision provenance at `~/git/papers/working/calculus-paper-spine-2026-05-28.md` and `~/git/papers/working/source-basis-discipline-synthesis.md`.

**Secondary cashout:**

- **Paper 28 (Zenodo Δt series), working slug *"The Lie Is Cheaper Than the Proof"*** — bridge artifact, interpretation layer. Discharges the antecedent the formal kernel is *structurally forbidden from asserting* (the kernel's institutional fence makes its results conditional; paper 28 argues the antecedent holds in the wild, with the 2 / 3 / 25–27 corpus as case-law evidence). Cites the preprint as its formal kernel rather than containing it. **Status: not started; gated on the preprint having a citable scaffold** (no paper-laundering-via-citation). Same spine page as above.

**Scope discipline.** The preprint inherits the kernel's institutional fence — *"kernel-legible all-green verdict, NOT substantively-grounded legitimacy."* Paper 28 is the home for the substantive-grounding argument. Separating these is what makes both papers honest. The punchy slug deliberately lives on paper 28 (where rhetoric is contribution); the preprint's sober title is genre-appropriate for cs.LO.

**Related records:** spine page (above); tier map `~/git/papers/working/tooltheory/calculus-2-tier-map-2026-05-28.md`; ρ-drop decision `~/git/papers/working/tooltheory/safety-bridge-rho-drop-decision-2026-05-28.md`; Calculus 2.0 exit criteria reconciliation `~/git/papers/working/calculus-2-exit-criteria.md` (status update 2026-05-29); kernel-overlap audit `~/git/papers/working/tooltheory/safety-bridge-kernel-overlap-audit-2026-05-29.md` (closes the second safety-axis minting gate). The "Calculus 2.0" label as a unifying-promotion target is moot post-2026-06-03 synthesis closure (see `~/git/papers/working/source-basis-discipline-synthesis.md`); the composition and self-amendment axes are now species under the "disciplined premise production" umbrella, not pending unification gates.

## Open / axiomatic boundaries

- **`persistence_normalizes` axiom** in `PersistenceModel.lean` — intentionally weak, marks where static formalization ends. Relevant to the dynamic-claims roadmap (three-bucket split: explicit specifications / transition-system or temporal model / simulation). See memory `project-lean-dynamic-roadmap.md` in the papers project memory.

## Change log

- **2026-04-19** — File created. Based on Lean state as of commits `cfc612f` / `d6adbbc` / `6bc8037` / `18c1f7c`.
- **2026-04-20** — P22 reclassification: dropped coupling-family tie-in (too forced); kept `persistence_normalizes` as primary anchor and three-terminal-families as resonance only. Mirrors the index update in the papers repo.
- **2026-04-20** — P18 Appendix A drafted and mapped. `PersistenceModel.lean` now has an explicit appendix landing in P18 (v1.1 candidate, not yet pushed to Zenodo). Specific theorem pointers cited in the appendix: `idle_preserves_capacity`, `hysteresis_without_warn`, `hysteretic_absorbing_internal`, `reattach_from_hysteretic_fails`, `repair_produces_restructured_not_aligned`, `repair_capacity_is_configured`, `restructured_can_fail_again`.
- **2026-04-22** — Added `OpsMasking.lean` entry (P23 primary cashout, case (i) only — bridge artifact + certify), `RepairOperator.lean` entry (no current paper cashout; formalizes `working/sovereign-repair-operator.md`), and Companion simulations section listing `ops_continuity.py` (P23) and `shared_vision.py` (P24). Header path in `OpsMasking.lean` updated from stale `working/ops-non-self-identical-controller.md` to `preprint/23-non-self-identical-controller/non_self_identical_controller.md` reflecting the preprint promotion. Mirrors the index update in the papers repo.
- **2026-04-28** — Added `Paper24SharedVision.lean` (P24 primary cashout — sharpen + certify). Algebraic shard for §4 metric probes and Theorems 3–4; corrects the Proposition 2 sign in the paper. Wired into `LeanProofs.lean`.
- **2026-04-30** — Added Admissibility kernel (`Admissibility/Authority.lean`, `StateTransition.lean`, `Derivation.lean`, `Execution.lean`) under new "infrastructure substrate" framing — no paper cashout, Governor-neutral. All four wired into `LeanProofs.lean` root. New `Admissibility/README.md` documents the four-module breakdown. Mirrors the index update in the papers repo.
- **2026-05-03** — Added `Paper25EpistemicBorderControl.lean` (P25 primary cashout — certify + bridge artifact + sharpen). Five theorems: `replicateRows_mulVec_apply`, `ker_replicateRows_eq_ker`, `replicateRows_transpose_mul` (§5 sibling-vs-§N adjudication, including the Gramian scaling identity $(\mathbf{1}_N \otimes M)^\top (\mathbf{1}_N \otimes M) = N \cdot M^\top M$); `obsEquiv_policy_same`, `target_distinct_policy_same` (§3.1 Theorem 1 epistemic-access core, with the target inequality as intentionally-unused hypothesis). Wired into `LeanProofs.lean` root; `lake build` green; no `sorry`. Companion to the §5 clarifying paragraph in `epistemic_border_control.md` (subspace-vs-vector precision, Lean repository pointer). Mirrors the index update in the papers repo.
- **2026-05-01** — Added `Admissibility/Corrective.lean` as fifth kernel module. Corrective monotonicity layer: `classify : Step → StepClassification` (enforcement surface), `WeaklyLessPermissive` preorder, `CorrectiveMonotone env` obligation, `RecoveryEnv` gate (operationally-required-at-recovery-boundary), `corrective_no_authority_laundering` corollary. No global axiom; obligation is bundled per the kernel's house style. Wired into `LeanProofs.lean` root; `lake build` green. `Admissibility/README.md` updated for the five-module breakdown. Companion working note at `~/git/papers/working/admissible-recovery-semantics.md`. Same-day, P27 skeleton (`Admissibility.lean`) sorry-eliminated: three real proofs against the local `admissible` definition, two `True`-placeholder discharges with deferred-real-statement docstrings (pending substrate-accusation / causal-binding predicates). P27 skeleton remains unwired — sorry-elimination does not imply wiring. Mirrors the index update in the papers repo.
- **2026-05-07** — Added `Admissibility/CorrectiveBoundary.lean` as boundary-result sibling. Removed the previously-admitted investigative null `corrective_then_forward_is_not_monotone` (`sorry`-bearing theorem) from `Corrective.lean`; replaced with comment-shape pointing to the boundary module. Boundary module proves model-dependence: identity-store model has the existential FALSE for any env; witness model (nondegenerate ops + verdict-sensitive `BasisDerivation`) has it TRUE with a concrete witness; abstract `NondegenerateStoreSemantics` structure + parametric theorem `corrective_then_forward_is_not_monotone_of_nondegenerate`; `witness_satisfies_nondegenerate` certifies the witness model. The abstract kernel's existential remains formally undecidable; the boundary module exhibits both possible answers without committing the abstract kernel to either. Wired into `LeanProofs.lean`. Repo is now sorry-free. CLAIM-REGISTER: A1 resolved, #14 added, summary table updated. Companion working-note update: `~/git/papers/working/nondegenerate-store-semantics.md` Gate A closing note.
- **2026-05-08** — Added `Admissibility/WitnessInvariance.lean` as boundary-primitive sibling. Origin: multi-model distillation of McGee/Zhang/Blank 2026 *Cognitive Science* 50(3) "Evidence Against Syntactic Encapsulation in Large Language Models." Two namespaces: abstract `Encapsulated` / `MovesUnderExcludedPerturbation` definitions + boundary theorem `moves_implies_not_encapsulated` + symmetric reading `encapsulated_implies_not_moves`; toy counterexample namespace exhibiting `selectivity_does_not_imply_encapsulation`. Doctrine: prove the boundary claim, not the Wiley paper. Supplies missing invariance-discipline rung for the admissibility apparatus's witness-validation vocabulary. Wired into `LeanProofs.lean`; `lake build` green; sorry-free. Companion working note: `~/git/papers/working/primitives/witness-invariance-failure.md` (candidate primitive, default density). `Admissibility/README.md` updated with the new sibling section. Subsequent same-day refinements: typed perturbation-relation form (`EncapsulatedWrt` parameterized by an allowed-perturbation relation, not just a type — per ChatGPT 2026-05-08 sharpening); `encapsulated_wrt_mono` refinement-monotonicity; `encapsulated_wrt_iff_relational` bridge; regime-bounded form (`EncapsulatedWithinRegime`, `MovesWithinRegime`, boundary theorem) — operator-override-restored: `encapsulated_within_universal_regime_iff_encapsulated_wrt` and `encapsulated_within_regime_mono` per `feedback-conservative-trim-override.md`.
- **2026-05-08** — `PersistenceModel.lean` quantitative burn + realization cluster (Phases A, B, C per ChatGPT 2026-05-08 routing). Phase A: `commit_burns_exactly` (additive form, isolates Nat-truncation boundary), `commitsToHysteretic` (closed-form commit count with cap=0 special case), `commitsToHysteretic_monotone` (non-strict — *less rollback capacity is no slower to hysteretic failure*). Phase B: `commitsToHysteretic_strict_mono` (positivity-bounded — strict requires `0 < cap₂` to exclude the genuine tie at boundary `cap₂ = 0, cap₁ = burnRate`); `post_repair_faster_to_hysteretic` (one-line corollary requiring `0 < cfg.repairCapacity ∧ cfg.repairCapacity + cfg.burnRate ≤ initialCapacity`). Phase C (trace realization bridge): `step_commit_low_terminates` and `step_commit_high_continues` helpers plus strong induction on `rollbackCapacity` (via `Nat.strongRecOn`) yield `commitsToHysteretic_realizes` — the bridge from closed-form commit count to actual `run`-trace semantics. Recurrence `commits(cap) = commits(cap - burnRate) + 1` for `cap > burnRate` proven inline via `Nat.add_div_right` rather than as a third helper (per ChatGPT's two-helper cap). `post_repair_trace_faster` corollary lands the doctrine claim at the trace level: composes the Phase B strict commit-count inequality with two applications of `commitsToHysteretic_realizes` to yield `∃ kR kI, kR < kI ∧ run-trace-ends-in-hysteretic` for both post-repair and initial. Closes the ladder from capacity arithmetic → commit-count horizon → strict-faster theorem → run-trace realized faster. Provenance: ChatGPT caught a falsity in the originally-proposed `strict_mono` (boundary `cap₂ = 0, cap₁ = burnRate` falsifies it under the cap=0→1 convention); corrected hypothesis form preserves the doctrine. Wired into `LeanProofs.lean`; `lake build` green; sorry-free.

- **2026-05-08** — Added `Admissibility/CorrectiveBoundary.lean` Site 3 (`Witness.DoesNotPreBlock` predicate naming the structural condition the witness construction relies on; `Witness.witnessCorrective_doesNotPreBlock_witnessClaim` discharges via concrete `999 ≠ 1`). Site 2 inspection (factor `mixed_class_witness` via `DoesNotPreBlock`): no Lean change — the abstract `NondegenerateStoreSemantics` layer cannot decompose the conclusion further without env-specific commitments; refusing to launder the conclusion into a shiny new predicate is the discipline (filed as `feedback-failed-factoring-as-honest-boundary.md`). Site 1: prose honesty patch — top doc-block extended with structural-mirror section (what's preserved vs collapsed); `mixed_class_witness` field comment forward-points to `Witness.DoesNotPreBlock`. Three-site batch closed.

- **2026-05-29** — Added safety-bridge family section (paper anchor: planned formal-methods preprint "An Admissibility Calculus: Authorization, Safety Bridges, and Value Decay"; secondary anchor: paper 28). Previously the safety-bridge work had no paper anchor; the spine-page decision at `~/git/papers/working/calculus-paper-spine-2026-05-28.md` resolved the topology fork (Fork B — preprint as sibling outside Δt numbering; paper 28 as interpretation paper that cites it). Eight modules covered (brick 0 + bricks 1a/1b + brick 2 + tier-1 ledger): `AuthorizedNotSafe(Witness)`, `SafetyBridge(Witness)`, `AuthorizedStepNotSafe(Witness)`, `SafetyTrajectory`, `AttestationLedger`. Status: formalized YES; preprint scaffold pending. Earned preprint status via one irreducible theorem family (trajectory triple + no-lift) replicated across two distinct witnesses (receipt-poison miniature + attestation-ledger).
