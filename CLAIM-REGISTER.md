# Claim Register — Post-Formalization Audit

Scoped to claims touching: Δh, Δc, detachment, rollback, closure,
sink/attractor language, terminal families, and "long enough."

Generated 2026-04-03 after static topology and persistence model results.

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
| **Status** | **BROKEN** |
| **Tool** | Lean (TaxonomyGraph.lean — closure classification) |
| **Fix** | Static topology yields three terminal families {Δg,Δa}, {Δx}, {Δh}. Δs and Δk cannot reach Δh. Universalization of Δh must be stated as a temporal hypothesis, not a graph fact. |

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

---

## Summary

| Status | Count | Action |
|--------|-------|--------|
| BROKEN | 2 | Rewrite with corrected claims |
| STALE | 3 | Tighten framing, remove temporal conflation |
| SOUND | 6 | No change; some need cross-referencing |
| OPEN | 1 | Δc→Δh dynamics (partially formalized, external repair next) |

Entries #1–#10 are from the original 2026-04-03 audit, scoped to claims touching Δh, Δc, detachment, rollback, closure, sink/attractor language, terminal families, and "long enough." Entries #11–#12 (added 2026-05-03) cover Paper 25's §5 sibling-vs-§N algebraic adjudication and §3.1 Theorem 1 epistemic-access core, formalized in `LeanProofs/Paper25EpistemicBorderControl.lean`.

### Priority rewrites — DONE (2026-04-03)

1. **taxonomy-relationships.md:136** — ~~Kill "universal sink" framing~~ DONE. Replaced with three-terminal-family result + pointer to property-based definition.
2. **taxonomy-structured-pass.md:198 + :262** — ~~Drop "universal sink" from Δh role description~~ DONE. Changed to "persistence sink (one of three terminal families)" in both role description and classification summary.
3. **taxonomy-role-map.md:75** — ~~Promote buried good definition~~ DONE. Added Lean formalization result, three terminal families, and clarified temporal vs. graph distinction. Kept the self-referential persistence criterion as canonical.
4. **Implicit "prolonged detachment" assumption** — Addressed in PersistenceModel.lean invariant 5 and RESULTS memo. Prose in taxonomy files now references cumulative rollback depletion rather than contiguous duration.
