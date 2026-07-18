# Claim Register — Post-Formalization Audit

Scoped to claims touching: Δh, Δc, detachment, rollback, closure,
sink/attractor language, terminal families, and "long enough."

Generated 2026-04-03 after static topology and persistence model results.

**v13 custody correction:** claim status is unchanged. Current source paths
and stable/evidence roles follow
[`docs/V13-RELEASE-LEDGER.md`](docs/V13-RELEASE-LEDGER.md); dated release
records retain their archive-time labels. In particular, the v4-v7 substrate
now lives under `LeanProofs/CustodyIndexed/`, and finished fixtures are
`PUBLIC-EVIDENCE` rather than ANNEX/Scratch.

## Status key

- **BROKEN** — Lean directly falsified or the claim conflates proven-distinct concepts
- **STALE** — Not wrong, but uses framing that tonight's work showed is imprecise
- **SOUND** — Survives formalization; correctly framed
- **OPEN** — Not yet testable; needs future work

---

## Register

### 1. "Δh is the universal sink"

| Field | Value |
|-------|-------|
| **Location** | `working/cybernetic-failure-taxonomy/taxonomy-relationships.md:136` |
| **Claim** | "Δh is the universal sink — any failure that persists long enough becomes hysteresis" |
| **Bucket** | Was presented as structural; is actually temporal |
| **Status** | **BROKEN** as static pipeline topology. **OPEN** as an unconditional temporal-attractor claim. Potentially **SOUND** only as a *conditional dynamics theorem* — one requiring explicit persistence / no-correction / operational-use / burn or lock-in hypotheses (not asserted anywhere as of 2026-06-29). |
| **Tool** | Lean (TaxonomyGraph.lean — closure classification) |
| **Fix** | Static topology yields three terminal closure families {Δg,Δa}, {Δx}, {Δh}; Δs and Δk cannot reach Δh (`ds_not_reaches_dh`/`dk_not_reaches_dh` via forward-closed lanes). That partition is the public result. **2026-06-29: demoted the `axiom persistence_normalizes : ∀ d, d≠.dh → True`** (a `True`-bodied placeholder polluting the repo axiom surface) to a non-asserting `TemporalAttractorSubstrate` socket; the prose "TRUE as a temporal attractor claim" is corrected to OPEN. Any universalization of Δh must be a conditional temporal theorem over an explicit dynamics substrate, not a graph fact and not an axiom. |
| **Robustness (Step 4, 2026-06-29)** | The non-reachability is **edge-policy-relative**, and that is now itself a theorem. Reachability is parameterized over the edge relation (`ReachableBy E`, adapters `reachable_to_by_edge`/`by_edge_to_reachable`); the negative results route through the generic `no_reach_of_closed_lane` (forward-closed lane + src inside + dst outside ⇒ unreachable — the receipt names the hinge). Fenced counterfactuals (`CounterfactualEdges.edgePlusDmDc`/`edgePlusDxDc`, no mutation of canonical `edge`) prove the result FLIPS under one admitted handoff edge: `ds_reaches_dh_with_dm_dc` (Δs→Δm→Δc→Δh under Δm→Δc) and `dk_reaches_dh_with_dx_dc` (Δk→Δx→Δc→Δh under Δx→Δc). **Interpretation:** the verified static result is a closure-partition theorem for the *declared* graph, not a universal theorem over all plausible edge-admission policies. (`no_reach_of_closed_lane` is also the conversion-router #4 delta — one pattern, two surfaces.) |

### 2. Δh property-based clarification (contradicts #1)

| Field | Value |
|-------|-------|
| **Location** | `working/cybernetic-failure-taxonomy/taxonomy-role-map.md:72-75` |
| **Claim** | "Δh as 'universal sink' means it's the destination of uncorrected failures, not that every old failure is hysteretic. Discrimination criterion: pathological when persistence mechanism is self-referential rather than environment-referential." |
| **Bucket** | Structural (property-based definition) |
| **Status** | **SOUND** — but buried under the broken version in #1 |
| **Tool** | n/a |
| **Fix** | Promote this as the canonical definition. #1's temporal framing should be replaced with this property-based one. |

### 3. "Prolonged detachment leads to reset failure"

| Field | Value |
|-------|-------|
| **Location** | Implicit across taxonomy prose; explicit in persistence model design |
| **Claim** | Sustained contiguous detachment is what produces hysteresis |
| **Bucket** | Was temporal-spec; partly falsified |
| **Status** | **BROKEN** (as necessary condition) |
| **Tool** | Lean (PersistenceModel.lean — invariant 5: hysteresis_without_warn) |
| **Fix** | Reset failure is driven by cumulative rollback depletion under detached commits. Prolonged contiguous detachment is sufficient but not necessary. Repeated short episodes suffice. |

### 4. "Long enough" temporal threshold (meta-representation)

| Field | Value |
|-------|-------|
| **Location** | `preprint/06-temporal-closure-requirements/SI-C_Theory_Comparison.md:63-68` |
| **Claim** | "Meta-representation requires temporal persistence. A higher-order thought about a first-order state needs both to persist long enough for the relationship to exist." |
| **Bucket** | Temporal-spec |
| **Status** | **STALE** |
| **Tool** | Prose revision |
| **Fix** | Reframe as coexistence constraint: both states must be simultaneously available in the representational substrate. "Long enough" is implementation, not the theoretical claim. |

### 5. Attractor basin geometry (Second Law)

| Field | Value |
|-------|-------|
| **Location** | `preprint/02-second-law-organizations/second_law.md:242-293` |
| **Claim** | Basin A (high fidelity) is narrow, Basin B (low fidelity) is broad. Stochastic transitions preferentially move A→B because Ω_B >> Ω_A. Return probability vanishes. |
| **Bucket** | Structural (phase-space geometry) |
| **Status** | **SOUND** — the asymmetry is geometric, not temporal |
| **Tool** | n/a |
| **Fix** | None needed for the core claim. Minor: "settling into" (line 281) should say "accessible equilibrium set under constraints" to avoid temporal implication. |

### 6. "Long Quiet" phenomenological signature

| Field | Value |
|-------|-------|
| **Location** | `preprint/02-second-law-organizations/second_law.md:771-782` |
| **Claim** | "Everything seems fine while Δt increases (metastable in Basin A under increasing effective heat)" |
| **Bucket** | Temporal-spec |
| **Status** | **SOUND** — correctly framed as temporal phenomenon from static cause |
| **Tool** | n/a |
| **Fix** | None. |

### 7. Metastability guardrail

| Field | Value |
|-------|-------|
| **Location** | `docs/method/falsification.md:53-62` |
| **Claim** | Metastable requires: not in equilibrium, maintained by named active buffer, identifiable domain-break condition. "If you cannot name the buffer, the serialization mechanism, and the domain-break condition, you do not get to use the word." |
| **Bucket** | Structural (property-based definition) |
| **Status** | **SOUND** |
| **Tool** | n/a |
| **Fix** | None. This is the correct framing. Cross-reference from Δh claims to reinforce. |

### 8. Δh lateral effects ("normalizing what should be temporary")

| Field | Value |
|-------|-------|
| **Location** | `working/cybernetic-failure-taxonomy/taxonomy-structured-pass.md:194-198` |
| **Claim** | "Δh doesn't generate new failure types so much as it locks in existing failures and then erodes the ability to recognize them." Role: "Universal sink + lateral generator." |
| **Bucket** | Ambiguous — mixes state description with causal process |
| **Status** | **STALE** |
| **Tool** | Prose revision |
| **Fix** | Distinguish: (a) Δh as a state (self-referential persistence) vs. (b) Δh→Δn, Δh→Δc as lateral reinforcement (already modeled separately as `reinforces` relation in Lean). Drop "universal sink" label. |

### 9. "Designed never to remain itself long enough"

| Field | Value |
|-------|-------|
| **Location** | `working/claimant-transition-addendum.md:211-217` |
| **Claim** | "It is not a worker because we designed it never to remain itself long enough to complain." |
| **Bucket** | Normative (governance/rights framing) |
| **Status** | **STALE** |
| **Tool** | Prose revision |
| **Fix** | "Long enough" obscures the structural claim: the system lacks the invariants necessary for persistent identity. Reframe as "designed to lack the structural conditions for self-continuity." |

### 10. Capacity-constrained stability (Paper 9)

| Field | Value |
|-------|-------|
| **Location** | `preprint/09-capacity-constrained-stability/capacity_constrained_stability_complete_paper.md:279-285` |
| **Claim** | "When shock arrival rate during the response window exceeds processable volume, the institution cannot maintain function long enough to implement adaptive responses." |
| **Bucket** | Temporal-spec (temporal outcome from static cause) |
| **Status** | **SOUND** — correctly separates static constraint from temporal consequence |
| **Tool** | n/a |
| **Fix** | None. |

### 11. P25 §5 algebraic adjudication: aggregation does not rotate the observability subspace

| Field | Value |
|-------|-------|
| **Location** | `preprint/25-epistemic-border-control/epistemic_border_control.md`, §5 ("Algebraic adjudication" subsection through the closing core line) |
| **Claim** | "Aggregation improves SNR; it does not rotate the observability subspace." Stacked-witness observability matrix preserves the kernel; least-observable subspace is invariant under homogeneous replication. Paper 24's clean aggregation is therefore not sufficient for substitution-freedom. |
| **Bucket** | Structural (linear-algebra adjudication of a sibling-vs-nested decision) |
| **Status** | **SOUND** — kernel preservation and Gramian scaling both proven |
| **Tool** | Lean (`Paper25EpistemicBorderControl.lean` — `ker_replicateRows_eq_ker`, `replicateRows_transpose_mul`) |
| **Fix** | Subspace-vs-vector precision added 2026-05-03 as a clarifying paragraph in §5: when the smallest singular value is degenerate, the invariant is the unobservable subspace, not a privileged $v_\text{min}$ vector. Explicit Gramian identity $(\mathbf{1}_N \otimes O_T)^\top (\mathbf{1}_N \otimes O_T) = N \cdot O_T^\top O_T$ included. |

### 12. P25 §3.1 Theorem 1: observation-equivalent states get identical control sequences

| Field | Value |
|-------|-------|
| **Location** | `preprint/25-epistemic-border-control/epistemic_border_control.md`, §3.1 ("Theorem 1 (static observability-asymmetry substitution)") |
| **Claim** | "Any controller whose policy depends only on $\{y_0, \ldots, y_{T-1}\}$ assigns the same control action sequence to $x$ and $x'$" when the observation trajectories agree. The structural refusal: observation geometry forecloses target regulation regardless of controller sincerity. |
| **Bucket** | Structural (epistemic-access lemma; the policy has no distinguishing input) |
| **Status** | **SOUND** in its load-bearing core — observation-equivalence ⇒ policy-equivalence is `rw [h]` |
| **Tool** | Lean (`Paper25EpistemicBorderControl.lean` — `obsEquiv_policy_same`, `target_distinct_policy_same`) |
| **Fix** | None to the structural refusal claim. The paper's prose proof additionally hand-waves a closed-loop induction (closed-loop observations track open-loop ones under common controller action). That induction is correct but is *not* the load-bearing claim; the structural refusal stands without it. The Lean theorem isolates the load-bearing core. The corollary `target_distinct_policy_same` carries `target q x ≠ target q x'` as an intentionally-unused hypothesis: the policy never sees the target, so target inequality cannot break policy equality. |

### 13. Corrective monotonicity (non-laundering)

| Field | Value |
|-------|-------|
| **Location** | `LeanProofs/Admissibility/Corrective.lean` (`corrective_monotone`, `corrective_no_authority_laundering`) |
| **Claim** | "Corrective steps cannot widen the authorized-action set; recovery cannot launder a revoked basis through to authorization for the same K." |
| **Bucket** | Structural (kernel obligation) |
| **Status** | **OPEN** — obligation declared, not yet discharged for the abstract kernel |
| **Tool** | Lean (Admissibility/Corrective.lean) |
| **Fix** | Theorems are stated relative to a `CorrectiveMonotone env` witness, which any concrete `DerivationEnv` must construct. The witness is currently vacuously satisfiable for the abstract kernel because behavioral laws on `applyUpdate`, `appendGap`, and `appendRevocation` are not yet committed (`StateTransition.lean` leaves them as unconstrained `axiom`s). The formal debt is to state nondegenerate store laws and instantiate `BasisDerivation` against them; this does not wait on runtime adoption. Until then the abstract kernel pins the obligation's *shape* without yet ruling out laundering for any specific env. **Update 2026-05-07:** the previously-admitted investigative null `corrective_then_forward_is_not_monotone` (formerly entry A1) has been replaced by a positive boundary result in `LeanProofs/Admissibility/CorrectiveBoundary.lean`. See entry #14. |

### 14. Corrective+forward model-dependence (boundary result)

| Field | Value |
|-------|-------|
| **Location** | `LeanProofs/Admissibility/CorrectiveBoundary.lean` |
| **Claim** | The abstract kernel's existential `∃ env Γ sc sf, IsCorrective sc ∧ IsForward sf ∧ ¬ WeaklyLessPermissive env (applySteps Γ [sc, sf]) Γ` marks a genuine model-dependence boundary, not a vocabulary deficit. Identity store ops + arbitrary env make the existential FALSE; nondegenerate ops + verdict-sensitive env make it TRUE. |
| **Bucket** | Structural (parallel miniature kernel exhibits both possible answers) |
| **Status** | **SOUND** — model-dependence proved; abstract null replaced by boundary result; repo is sorry-free |
| **Tool** | Lean (`CorrectiveBoundary.lean`) — `Identity.corrective_then_forward_is_monotone_universally`, `Witness.corrective_then_forward_is_not_monotone`, `corrective_then_forward_is_not_monotone_of_nondegenerate` (parametric form), `witness_satisfies_nondegenerate` |
| **Fix** | None to the boundary claim itself. Provenance: ChatGPT's "prove the boundary, not the theorem" plan, 2026-05-07. The miniature kernel re-creates the abstract kernel's structure with concrete payload types (`PolicyStore := List Nat`, etc.) and parameterized store ops (`StoreOps` structure). Two model namespaces (`Identity`, `Witness`) prove the two possible answers. Abstract `NondegenerateStoreSemantics` packages the three commitments from `papers/working/nondegenerate-store-semantics.md` and the parametric theorem proves the existential follows from the structure. Witness model satisfies the abstract structure. The abstract kernel itself remains consistent with both the existential and its negation; that is the doctrinally-correct stance, and the boundary result is the positive content of the formerly-admitted null. |

### 15. PersistenceModel quantitative burn + realization cluster (P18 cashout)

| Field | Value |
|-------|-------|
| **Location** | `LeanProofs/PersistenceModel.lean` (`commit_burns_exactly`, `commitsToHysteretic`, `commitsToHysteretic_monotone`, `commitsToHysteretic_strict_mono`, `post_repair_faster_to_hysteretic`, `step_commit_low_terminates`, `step_commit_high_continues`, `commitsToHysteretic_realizes`, `post_repair_trace_faster`) |
| **Claim** | "After external repair, the system reaches hysteretic in strictly fewer commits than the original journey, when repair grants positive capacity at least one full burn-unit below baseline." Closed-form commit count `commitsToHysteretic burnRate cap` is defined; strict commit-count monotonicity holds under `0 < repairCapacity ∧ repairCapacity + burnRate ≤ initialCapacity`; trace-level realization holds — replicating `commitsToHysteretic`-many `.commit` events from a detached state lands in `hysteretic`. |
| **Bucket** | Structural (closed-form arithmetic + state-machine realization) |
| **Status** | **SOUND** through the full ladder: capacity arithmetic → commit-count horizon → strict-faster theorem → run-trace realized faster. `post_repair_trace_faster` (added 2026-05-08, post-Phase-C) composes the Phase B strict inequality with two applications of `commitsToHysteretic_realizes` to land the doctrine claim at trace level. |
| **Tool** | Lean (`PersistenceModel.lean`, added 2026-05-08, three phases) — eight new theorems landed sorry-free; companion change-log entry in PAPER-MAP. Realization proof uses `Nat.strongRecOn` for strong induction on `rollbackCapacity`, with two helpers (`step_commit_low_terminates`, `step_commit_high_continues`) and inline recurrence via `Nat.add_div_right`. |
| **Fix** | The originally-proposed `commitsToHysteretic_strict_mono` was *false* under the draft's own `cap = 0 → 1` convention: counterexample at `cap₂ = 0, burnRate = 3, cap₁ = 3` (both sides take 1 commit, hypothesis `cap₂ + burnRate ≤ cap₁` holds, but strict `<` fails). ChatGPT caught it during inspection. Corrected hypothesis form requires `0 < cap₂` to exclude the genuine boundary tie, preserving doctrine: *"less capacity is no slower (non-strict) under any reduction; strictly faster (strict) when the reduction is positive and exceeds one burn-unit."* The boundary case is operationally meaningful — at `cap = burnRate` the system already burns out on first commit, so no improvement is possible from less capacity at that boundary. The realization bridge connects this commit-count arithmetic to actual `run` traces ending in `hysteretic`, completing the formalization stack from prose doctrine through closed-form arithmetic through state-machine semantics. |

### 16. WDC 2.0: model-independent normalization (admitting-class)

| Field | Value |
|-------|-------|
| **Location** | `LeanProofs/Witnessed/AbstractNormalization.lean`, `LeanProofs/Witnessed/CommutesNecessity.lean`, `LeanProofs/Witnessed/Normalization.lean` |
| **Claim** | The carry/weaken normal-form factorization is earned OFF the freshness model: `normal_form_iff_of_commutes` proves `PaidFrom (Step C W) a c ↔ ∃ z, Chain C a z ∧ Chain W z c` for any two-family bridge whose families satisfy the local commutation law `Commutes C W`. The freshness `bridge_path_normal_form` is rerouted to be its `(CarryStep, WeakenStep)` instance (`perm_weaken_carry` discharges `Commutes`); name/signature/`[propext]` footprint unchanged. `commutes_is_necessary` proves the law is load-bearing — a concrete system where `Commutes` fails admits a paid path with no carry-then-weaken factorization. |
| **Bucket** | Structural (admitting-class theorem + necessity counterexample; the Frontier Register's 2.0 criterion #1) |
| **Status** | **SOUND** — `normal_form_iff_of_commutes` and `commutes_is_necessary` axiom-free; `bridge_path_normal_form` re-attested at `[propext]` (unchanged) through the abstract route. WDC-surface footprint gate green (12 receipts). |
| **Tool** | Lean — `AbstractNormalization.{Chain, Step, Commutes, normal_form_iff_of_commutes}`, `CommutesNecessity.commutes_is_necessary`, `Normalization.{commutes_carry_weaken, cchain_iff_chain, wchain_iff_chain, freshpath_iff_paidstep, bridge_path_normal_form}`. |
| **Fix** | None. Released as `v2.0.0` on 2026-06-29 (peeled tag target `b4bd02b`) after operator ratification. The model-specific `normalize`/`bubble` survive only as the route for the cruder two-edge corollary. This is the reserved WDC structural milestone: model-independent admitting-class normalization plus the load-bearing necessity counterexample. It is **not** a cut-elimination release and does not claim universal normalization. WDC-surface cleanliness remains footprint-gated; repo-wide axiom classification is recorded by the audit fence. |

### 17. v11 — Occurrence-Exact Paid Recomposition

| Field | Value |
|-------|-------|
| **Location** | Stable core: `LeanProofs/Witnessed/PaidRecomposition/Payment.lean`, `LeanProofs/Witnessed/PaidRecomposition/Catalog.lean`, and `LeanProofs/Witnessed/PaidRecomposition.lean`. Public evidence outside the stable root: `Applications/ResourceTraceOneCrossing.lean`, `Countermodels/EndpointCompleteness.lean`, and `Applications/FiniteSupportOneCrossing.lean`; the last now imports `LeanProofs/CustodyIndexed/FiniteSupportChecker.lean`. |
| **Claim** | Ordered payments admit proof-relevant, occurrence-indexed checking with exact computed residue. Under exact attempt-level catalog completeness, paid global plans and paid catalog plans are equivalent without replacing native receipts, expected-payment evidence, payment traces, or residue. Endpoint-only completeness is insufficient. |
| **Bucket** | Structural (repository-integration theorem family: exact occurrence removal + exact-attempt catalog adequacy + premise-ablation countermodel) |
| **Status** | **SOUND** — the stable family is Mathlib-free and promoted through `LeanProofs.Witnessed.PaidRecomposition`; `PaymentRefusal.sound`, `checkPayment_accepts_iff`, and `PaymentTrace.length_conservation` establish the submitted-payment boundary; `exact_catalog_adequate` establishes the catalog/global equivalence under `ExactPaidCatalogComplete`; `exact_complete_globalizes_refusal` is the scoped negative corollary. The endpoint countermodel proves the exact-completeness premise cannot be weakened to endpoint coverage. V12 corrects the unchanged inherited `NoFreeLift`/checker foundation to `PUBLIC-SHIPPED`, matching the exact stable closure v11 already used; this changes no claim or capability. |
| **Scope custody** | Three judgments remain distinct in the types: (1) acceptance of one submitted payment order (`checkPayment ... = .inl ...`, and separately a resident checker equation for one submitted trace); (2) no accepted realization in one named catalog (`¬ Nonempty (PaidCatalogPlan ... catalog ...)`); and (3) global nonexistence only from that catalog-relative refusal plus `ExactPaidCatalogComplete`. `ResourceCheckerExec.checkTrace = none` means only rejection of that submitted trace. |
| **Evidence** | `ResourceTraceOneCrossing` is public end-to-end corpus evidence: the resident `ResourceCheckerExec.Trace Nat` attempt and its native positive checker equation survive catalog conversion, with the exact expected map, payment trace, and residue. `EndpointCompleteness` is the premise-ablation countermodel. `FiniteSupportOneCrossing` is public evidence over the corrected public `CustodyIndexed.FiniteSupportChecker` foundation; it retains the native accepted/refused equations, positional provenance, native excess/offender meaning, exact payment residue, and accepted-path obligation residue. The fixed three-cycle fixture was intentionally not retained because it adds no independent evidence. |
| **Nonclaims / fix** | No new cut connective or proof calculus; no Hall, matching, 3DM, CSP, complexity, or plan-synthesis novelty. Occurrence indices are context-relative list positions, not persistent serials. `injectiveOn` is inherited plan plumbing and the singleton corpus supplies no nontrivial injectivity or matching evidence. Catalog refusal has no modeled transition, refusal debt-preservation, dynamic authority, resource creation, or temporal-debt semantics. PC-1 and PC-2 remain closed. Stateful bounded realization/refusal remains a separate next frontier. No fix required inside this claim boundary. |

### 18. v12 — Judgment Orientation

| Field | Value |
|-------|-------|
| **Location** | Stable root `LeanProofs/JudgmentOrientation.lean`; theorem modules `JudgmentOrientation/{Core,Attribution,Provenance,OriginSupport,Bridge}.lean`; fixtures in separately imported public evidence `Examples.lean`. Release inventory: [`docs/V12-RELEASE-LEDGER.md`](docs/V12-RELEASE-LEDGER.md). |
| **Claim** | Pure orientation can change inquiry posture but not protected judgment coordinates; a protected endpoint difference across a mixed trace localizes to a privileged change point; raw occurrence custody projects to an abstract finite-support join-semilattice in which exact-origin replay is idempotent; sequence append maps to support join and support cannot recover erased payload; composing the halves one way, an endpoint-visible orientation-invariant difference across an attributed mixed trace names a privileged step whose caller-supplied origin lies in the effective support of the trace's privileged provenance. |
| **Bucket** | Structural (write confinement + trace attribution + operational accounting + finite-support algebra + information-loss boundary + one-way composition) |
| **Status** | **SOUND** — `runRaw_protected` and its six no-mint/no-revoke corollaries establish confinement; `change_localizes_to_privileged` attributes an endpoint difference to a privileged step (without detecting later-reverted changes); provenance laws retain replay in raw custody while preserving one effective exact-origin contribution; `join_*`, `le_*`, `ofTrace_append`, and `ofState_run*` establish the semilattice and projection laws; `Bridge.changed_protected_has_supported_privileged_origin` reuses the localization theorem through the `toMixed` erasure and discharges support membership through the public `ofTrace`/`Contains` algebra. Public evidence supplies the payload-information-loss counterexample, non-vacuity specimen, and converse refutation (`supported_origin_without_change`). The 13-receipt axiom footprint is enforced fail-closed by `scripts/check-judgment-orientation-footprint.sh` in CI. |
| **Scope custody** | `EffectiveSupport` has a private carrier representation and the stable root excludes fixtures. `MayOrient` carries reusable admission evidence, not linear spend. Origin IDs are caller-supplied; `AttributedStep.privileged` binds its `Occurrence` structurally at trace construction, so the bridge fabricates no origins and its converse is explicitly false. Origin authentication, Sybil resistance, common-cause independence, payload fidelity, privileged-step justification, and runtime correspondence are explicit nonclaims. |
| **Fix** | None inside the stated boundary. Core/Attribution/Provenance/OriginSupport promoted from skunkworks commit `4f8e076`; `Bridge` authored 2026-07-16 in the promotion review. Release publication was a separate operator act that changed no claim or custody fact; the frozen v12 inventory is recorded in the release ledger. |

### 19. v14 rung 1 — PathVerdict domain transport and located diagnostics

| Field | Value |
|-------|-------|
| **Location** | Stable additions to the existing `path-verdict` root: `LeanProofs/Admissibility/PathVerdict/Domains.lean` (7 definitions, 24 theorems) and `LeanProofs/Admissibility/PathVerdict/Located.lean` (carried-id core, 12 theorems), both importing only `PathVerdict/Edges.lean`. Campaign inventory: [`docs/V14-READINESS-LEDGER.md`](docs/V14-READINESS-LEDGER.md). |
| **Claim** | Verdicts transport functorially between domain vocabularies: a domain map is pointwise on domain obstructions, fixes the core kernel, commutes with composition and the edge fold, and preserves AND reflects authority — re-domaining cannot launder (`mapDomain_authority_iff`, `core_mem_mapDomain_iff`). Mixed-domain paths live in the plain `Sum` coproduct with injections that fabricate no foreign sins and inherit the seal (`mixed_compose_authority_iff`). Separately, carried-id location decorates the obstruction log without touching the authority algebra: erasure recovers the Edges-layer fold exactly (`forget_foldLocated`), `foldLocated` artifacts are complete and sound about which edge sinned, and under a uniqueness hypothesis a log entry pins the edge's verdict exactly (`located_pinpoints`). Relocation is not repair (`mapId_forget`, `mapId_authority_iff`). |
| **Bucket** | Structural (functorial transport + coproduct mixing + diagnostic decoration with erasure tether) |
| **Status** | **SOUND** — all 36 receipts frozen and re-attested on arrival: 35 axiom-free, `mixed_compose_authority_iff` on `propext` only, no `sorryAx`. Enforced fail-closed by `scripts/check-pathverdict-footprint.sh` in CI. Promoted 2026-07-17 as rung 1 of the Admissibility Calculus campaign after hostile review of the skunkworks candidate packet; the dependency cone is exactly `Core ← Edges ← {Domains, Located}` with the two candidates as independent siblings. |
| **Scope custody** | Located ids are caller-supplied diagnostic labels, not authenticated origins or occurrence history. Soundness/completeness hold for `foldLocated` artifacts; raw `LocatedVerdict` construction can fabricate accusations (fold provenance is load-bearing — adverse specimens stay in research-tree evidence custody). Domain-value reflection through a map carries an explicit injectivity hypothesis; noninjective maps may merge labels but cannot launder. Positional indexing, demos, hostile fixtures, and the cross-calculus crossing adapter remain research-tree evidence, not public API. |
| **Nonclaims / fix** | No authenticated location, no unique-id preservation under arbitrary composition, no obstruction-dropping map (deliberately unrepresentable), no crossing checker promotion, and no admission of any later Calculus rung. No fix required inside this claim boundary. |

### 20. v14 rung 2 — the governed-family signature

| Field | Value |
|-------|-------|
| **Location** | New exact stable root `admissibility-calculus`: `LeanProofs/Admissibility/Calculus.lean` (aggregate) and `LeanProofs/Admissibility/Calculus/Core.lean` (namespace `Admissibility.Calculus`), import-free below Lean core. Campaign inventory: [`docs/V14-READINESS-LEDGER.md`](docs/V14-READINESS-LEDGER.md). |
| **Claim** | One structure fixes the bounded contract of a governed admissibility family: claim-indexed witness and refusal **data** (`Claim → Type`, so proposition-squashing is rejected by the sort checker), three separate proposition-valued books (standing, custody, obligation) with no conversion from any book to authority, witness/refusal exclusivity, and a total decision returning the native evidence. `Authority` is derived — `Nonempty (Witness c)` — with no alternative introduction rule. Six generic laws: refusal refutes authority; authority requires standing and preserves custody; squashed authority has no multiplicity (definitionally, by `rfl`); the decision is faithful in both directions; and no Boolean check factoring through a projection that collapses a witnessed claim into a refused claim can be a faithful authority judge (`no_claim_erasing_check_is_faithful`). |
| **Bucket** | Structural (signature contract + derived authority + generic anti-collapse laws) |
| **Status** | **SOUND** — all six receipts axiom-free (no `propext`, `Quot.sound`, `Classical.choice`, or `sorryAx`; Mathlib-free; zero imports), enforced fail-closed by `scripts/check-calculus-footprint.sh` in CI. Promoted 2026-07-17 as rung 2 after hostile review of the skunkworks candidate packet; the twelve-receipt hostile audit (book separation, obligation non-disposal, witness multiplicity, two-sided decision coherence, dependent refusal indexing, claim erasure vs. a faithful full-claim control) and the Prop-squashing rejection probe remain research-tree evidence. `no_claim_erasing_check_is_faithful` is the operator-ratified name, renamed before the freeze. |
| **Scope custody** | The signature is universe 0: `Claim` and every witness/refusal type inhabit `Type`, not a polymorphic `Type u`; universe polymorphism is a separately reviewed redesign, and no claim is made that the receipts transport unchanged to arbitrary universes. `Admissibility.Calculus` is the construction namespace of the campaign's unified object — an address, not a completion claim; the capital-C claim stays gated on rung-7 ratification. Obligation carries no generic lifecycle law (family-native). The erasure theorem condemns only claim-collapsing projections; a full-claim checker remains faithful. |
| **Nonclaims / fix** | No funnel, lossless encoding, composition operator, comparison law, crossing, generic origin/history authentication, generic obligation lifecycle, arbitrary-family decision engine, unbounded reachability result, runtime correspondence, or later-rung admission. `Authority` intentionally forgets witness multiplicity; consumers that count must count native witness data. No fix required inside this claim boundary. |

---

## Admitted statements

Theorems intentionally admitted via `sorry`, separate from the BROKEN / STALE / SOUND / OPEN axis.

**As of 2026-05-07: zero admitted statements. The previously-admitted A1 (`corrective_then_forward_is_not_monotone`) has been replaced by a positive boundary result in `LeanProofs/Admissibility/CorrectiveBoundary.lean`.** See entry #14. The abstract kernel's `Corrective.lean` retains the theorem's statement as a comment-shape with a pointer to the boundary module; the existential remains formally undecided in the abstract kernel itself, but the model-dependence is proved.

### A1. `corrective_then_forward_is_not_monotone` (resolved 2026-05-07)

| Field | Value |
|-------|-------|
| **Original location** | `LeanProofs/Admissibility/Corrective.lean:283` (theorem with `sorry`, since removed) |
| **Type** | Investigative null (existential whose truth value is undecidable in the abstract kernel) |
| **Resolution** | Replaced 2026-05-07 by a positive model-dependence boundary result. The `sorry`-bearing theorem is removed; theorem statement preserved in `Corrective.lean` as a comment-shape pointing to `CorrectiveBoundary.lean`. The abstract existential remains undecidable under the abstract kernel's `axiom`-typed store ops — but the boundary module proves this undecidability is *genuine model-dependence*, exhibiting both possible answers in a parallel miniature kernel. |
| **What replaced it** | See entry #14 for the boundary result. |

---

## Summary

| Status | Count | Action |
|--------|-------|--------|
| BROKEN | 2 | Rewrite with corrected claims |
| STALE | 3 | Tighten framing, remove temporal conflation |
| SOUND | 14 | No change; some need cross-referencing (incl. #16 WDC 2.0 normalization, #17 v11 paid recomposition, #18 judgment orientation, #19 v14 rung-1 PathVerdict domain transport, and #20 v14 rung-2 governed-family signature) |
| OPEN | 2 | Universal Δh temporal-attractor claims remain open despite #15's completed quantitative-burn and trace-realization slice; corrective monotonicity remains an abstract obligation pending concrete store-operation laws |
| ADMITTED | 0 | (was 1; A1 resolved 2026-05-07 via boundary result, see #14) |

Entries #1–#10 are from the original 2026-04-03 audit, scoped to claims touching Δh, Δc, detachment, rollback, closure, sink/attractor language, terminal families, and "long enough." Entries #11–#12 (added 2026-05-03) cover Paper 25's §5 sibling-vs-§N algebraic adjudication and §3.1 Theorem 1 epistemic-access core, formalized in `LeanProofs/Paper25EpistemicBorderControl.lean`. Entry #13 (added 2026-05-06) records the corrective-monotonicity obligation shape pinned by `LeanProofs/Admissibility/Corrective.lean` — declared, not discharged in the abstract kernel. Entry #14 (added 2026-05-07) records the corrective+forward model-dependence boundary result in `LeanProofs/Admissibility/CorrectiveBoundary.lean`, which replaces the formerly-admitted A1. Entry #16 records the WDC 2.0 normalization milestone; entry #17 (added 2026-07-15) records the v11 occurrence-exact payment and catalog-adequacy theorem family with its evidence and scope fence; entry #18 (added 2026-07-16) records the v12 Judgment Orientation and exact-origin-support family; entry #19 (added 2026-07-17) records the v14 rung-1 PathVerdict domain-transport and located-diagnostics admission; entry #20 (added 2026-07-17) records the v14 rung-2 governed-family signature under the new `Admissibility.Calculus` construction namespace. The repo remains sorry-free.

### Priority rewrites — DONE (2026-04-03)

1. **taxonomy-relationships.md:136** — ~~Kill "universal sink" framing~~ DONE. Replaced with three-terminal-family result + pointer to property-based definition.
2. **taxonomy-structured-pass.md:198 + :262** — ~~Drop "universal sink" from Δh role description~~ DONE. Changed to "persistence sink (one of three terminal families)" in both role description and classification summary.
3. **taxonomy-role-map.md:75** — ~~Promote buried good definition~~ DONE. Added Lean formalization result, three terminal families, and clarified temporal vs. graph distinction. Kept the self-referential persistence criterion as canonical.
4. **Implicit "prolonged detachment" assumption** — Addressed in PersistenceModel.lean invariant 5 and RESULTS memo. Prose in taxonomy files now references cumulative rollback depletion rather than contiguous duration.
