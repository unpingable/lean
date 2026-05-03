# Paper Map

Module → paper crosswalk. Inverse of the paper-side index in the papers repo at `docs/formalization-index.md`.

Companion documents:

- `WHAT-THE-LEAN-STACK-PROVES.md` — module-level exposition of what each layer proves and what it killed
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

Five-state Δc→Δh dynamics. Cumulative rollback depletion under detached commits. External repair produces restructured, not aligned. Three-way recovery distinction. Kills "prolonged contiguous detachment causes reset failure" and "repair restores baseline."

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

Five modules forming a Governor-neutral authority kernel:

- `Authority.lean` — verdict algebra. `authorityVerdict : Basis × Precedence × Standing → AuthorityVerdict`. Authorized iff all three dimensions green.
- `StateTransition.lean` — partitioned governance state with isolation invariants. Only `Step.amendPolicy` mutates `PolicyStore`; `StepAllowed` gates raw mutation.
- `Derivation.lean` — read-side bridge from `GovState × Actor × AuthorityClaim` to component verdicts. Bundled-structure design (`BasisDerivation` etc. carry function + spec obligations). Revocation-shaped safety consequence.
- `Execution.lean` — `AuthorizedStep` bundles a step with both mutation standing (`StepAllowed`) and claim verdict (`authorityAuthorized`) by construction. Load-bearing theorem: revoked basis cannot produce an `AuthorizedStep`.
- `Corrective.lean` (added 2026-05-01) — corrective monotonicity layer. `classify : Step → StepClassification` (corrective / forward / neutral) is the enforcement surface; `WeaklyLessPermissive` is the preorder; `CorrectiveMonotone env` carries the proof obligation; `RecoveryEnv` bundles env + obligation and is the gate at which monotonicity becomes operationally required (recovery-facing APIs take `RecoveryEnv`, not raw `DerivationEnv`). Load-bearing corollary `corrective_no_authority_laundering` rules out same-basis laundering. Companion working note: `~/git/papers/working/admissible-recovery-semantics.md`.

**No paper cashout.** This is infrastructure substrate for a future Governor (`agent_gov`) implementation citation, not a paper-claim cashout. Concrete `claimForStep` resolvers and `AuthorityClaim` schema commitments belong in Governor's instantiation, not in the kernel. Documented here to keep the mapping complete.

Sibling to `LeanProofs/Admissibility.lean` (P27 obligation skeleton, namespace `P27`). Sorry-free as of 2026-05-01; three real proofs + two `True`-placeholder discharges pending sibling vocabulary; intentionally unwired (sorry-elimination does not imply wiring). The P27 skeleton and the Authority kernel are independent and address different layers (post-transition obligation accounting vs pre-action authorization). See `LeanProofs/Admissibility/README.md` for the five-module breakdown.

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
