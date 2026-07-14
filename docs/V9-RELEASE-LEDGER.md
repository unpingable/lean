# v9 Release Ledger — Dynamic Traces and Profile Semantics

**Release: v9.0.0 — Dynamic Traces and Profile Semantics** (*dynamic
execution over static witnesses, and checker-facing profile semantics*).
Prior release: v8.0.0 — Sequent Admissibility Island.

**Status: PREPPED, awaits operator mint.** Version strings bumped, docs
written, gates re-run green (2026-07-09). The mint chain — git tag + GitHub
release (which drives the Zenodo version DOI, per CHANGELOG) — is the
operator's step and has NOT been performed by tooling.

**Zenodo display metadata (v8 scar closed):** `CITATION.cff` drives the
Zenodo landing page (no `.zenodo.json` in this repo). Its `title`,
`abstract`, `version`, and `date-released` were updated to the v9 release in
this prep — not just the version fields. If the Zenodo record still shows a
stale title after mint, the record is editable post-publish without a new
DOI (see papers-repo Zenodo API workflow).

**Why a new major, not 8.1:** on this repo's release constitution ("major
proof campaign landed," not library-API semver), v9 opens the dynamic-claims
campaign — the first release whose center of gravity is *transitions*
(state-threaded traces) rather than static judgments. v8 is semantically
occupied by the ProofTheory island; the dynamic-trace material is a
different kind of object, and the roadmap (papers-repo dynamic-claims
three-bucket split) names it as its own campaign.

## The v9 claim (scoped, exact)

*A dynamic-step and trace layer over the public admissibility kernels in
which every hop carries the exact static `AuthorizedStep` witness it
consumes, with refusal theorems showing revocation and staleness reach
through to dynamic execution; plus a finite profile-checker semantics
specimen pinning the doctrine of the RRP admissibility gate.*

### Landed since v8.0.0 (commit `8fd73eb` + this prep)

| Item | File | Custody | Provenance |
| --- | --- | --- | --- |
| Dynamic trace layer | `LeanProofs/Admissibility/DynamicTrace.lean` | ANNEX | codex-derived (2026-07-08) |
| Freshness-gated dynamic discharge | `LeanProofs/Admissibility/FreshnessDynamicTrace.lean` | ANNEX | codex-derived (2026-07-08) |
| Revoked-standing execution theorem | `LeanProofs/Admissibility/Execution.lean` (additive) | PUBLIC-SHIPPED [1.0] | codex-derived (2026-07-08) |
| PathVerdict tier-1 continuation | `LeanProofs/Scratch/PathVerdict/{StandardObstructions,EvidencePromotionCoverage}.lean` | SCRATCH (fenced lib) | codex-derived (2026-07-08) |
| Mathlib import-surface split | `lakefile.toml` (`AdmissibilityCustodyAnnex`, `AdmissibilityMathlibIslands`, default-target change) | build surface | codex-derived (2026-07-08) |
| Import-closure gate | `scripts/check-mathlib-free-targets.sh` | audit script | this prep (2026-07-09; delivers the script the 07-08 changelog promised) |
| DeferredWitness reflection lemma | `LeanProofs/Admissibility/DeferredWitness.lean` (`firstViolation_none_iff_lawful`, `firstViolation_isSome_iff_not_lawful`) | ANNEX | this prep (GPT-Pro audit L1) |
| RRP profile semantics specimen | `LeanProofs/Admissibility/RRPProfileSpecimen.lean` | UNRATIFIED-CANDIDATE (unwired) | this prep (GPT-Pro audit L2) |
| Standing-backed claim specimen | `LeanProofs/Admissibility/StandingProfileSpecimen.lean` | UNRATIFIED-CANDIDATE (unwired) | this prep (GPT-Pro audit L3) |
| WLP append-ack specimen | `LeanProofs/Admissibility/WLPAppendAckSpecimen.lean` | UNRATIFIED-CANDIDATE (unwired) | this prep (GPT-Pro audit L4) |
| Bridge customs specimen | `LeanProofs/Admissibility/BridgeCustomsSpecimen.lean` | UNRATIFIED-CANDIDATE (unwired) | this prep (GPT-Pro audit L5) |
| Actor-trace specimen | `LeanProofs/Admissibility/ActorTraceSpecimen.lean` | UNRATIFIED-CANDIDATE (unwired) | this prep (GPT-Pro audit L6) |
| LocalBoundary concrete pressure test | `LeanProofs/Admissibility/LocalBoundaryPressure.lean` | UNRATIFIED-CANDIDATE (unwired, Mathlib-reaching) | this prep (GPT-Pro audit L7; operator-gated, gate opened 2026-07-09) |
| Scoped certification (*quis custodiet* seam) | `LeanProofs/Admissibility/ScopedCertification.lean` | UNRATIFIED-CANDIDATE (unwired) | this prep (operator-adjacent thought + ChatGPT-Pro sketch, 2026-07-09) |
| Spendability: eligibility/capacity split + fork residue (LA seam) | `LeanProofs/Admissibility/SpendabilitySpecimen.lean` | UNRATIFIED-CANDIDATE (unwired) | this prep (gap-closure pass, 2026-07-09; sources: LA README, budget-admission scenario, revoked-fork-residue hazard) |
| Custody freshness non-transitivity (NQ/Nightshift seam) | `LeanProofs/Admissibility/CustodyFreshnessSpecimen.lean` | UNRATIFIED-CANDIDATE (unwired) | this prep (gap-closure pass, 2026-07-09; sources: GAP-imported-basis-freshness, nightshiftd freshness.rs, NQ VERDICTS stale_testimony) |
| Temporal basis / time assurance (NQ seam, NQ-T4) | `LeanProofs/Admissibility/TemporalBasis.lean` | UNRATIFIED-CANDIDATE (unwired) | this prep (2026-07-09; operator-directed, formalize-before-NQ-implements; sources: NQ EVIDENCE_RETIREMENT_GAP, BASIS_STALE_CONTRACT, VERDICTS stale_testimony/cannot_testify, ChatGPT-Pro time-assurance track TA-0..5/NQ-T0..5) |
| CI release-envelope widening | `.github/workflows/lean_action_ci.yml` (full aggregate + islands + audit scripts) | CI surface | this prep |
| RRP↔Lean crosswalk | `docs/RRP-LEAN-CROSSWALK.md` | docs-only wiring | this prep (GPT-Pro audit L0) |

Key theorem receipts (all sorry-free, custody-classed):

- `DynamicTrace`: `revoked_basis_blocks_dynamic_step`,
  `revoked_standing_blocks_dynamic_step`,
  `step_allowed_without_authority_blocks_dynamic_step`,
  `traceHopsByActor_actor` / `anyActorTraceHopsByActor_actor`,
  `non_amend_trace_preserves_policy`.
- `FreshnessDynamicTrace`: `stale_observation_cannot_discharge_current_obligation`
  and the five per-failure-mode `*_cannot_discharge_current_obligation`
  theorems (expired / not-yet-valid / incoherent / not-precedes /
  divergence-excessive).
- `Execution`: `revoked_standing_cannot_be_authorized_step` (1.0, additive).
- `DeferredWitness`: `firstViolation_none_iff_lawful` — classifier ↔ spec.
- `RRPProfileSpecimen`: `mem_deriveClaims` (inversion),
  `missing_receipt_no_claim` (+ kind form), `cannot_testify_no_claim`,
  `stale_receipt_no_claim`, `revoked_basis_no_claim`,
  `effect_requires_claim`, `no_required_claim_no_permit`,
  `no_evidence_no_permit`, `profile_id_only_no_decision`,
  `digest_mismatch_refused`, `self_authorization_refused`.
- `StandingProfileSpecimen`: `schedule_is_not_standing`,
  `operator_ack_is_not_standing`, `model_output_is_not_standing`,
  `revoked_basis_no_standing`, `derived_claim_source_is_collector` /
  `derived_claim_basis_is_active` (inversions),
  `wrong_actor_not_permitted`, `wrong_project_not_permitted`,
  `other_actors_observation_never_permits` (end-to-end).
- `WLPAppendAckSpecimen`: `transport_evidence_mints_no_claims` (engine),
  `append_ack_alone_no_authorized_effect`,
  `publication_without_profile_claim_no_authorized_effect`,
  `append_ack_supports_custody_but_not_authority` (the seam's summary),
  `more_transport_evidence_never_authorizes`.
- `BridgeCustomsSpecimen`: `source_permit_alone_no_target_effect`,
  `source_refusal_no_local_claim` (refusals do not cross),
  `widening_cap_no_local_claim` + `bridge_claim_cannot_widen_scope`
  (inversion), `promoted_claim_confined_to_cap`,
  `target_profile_mismatch_no_local_claim`, positive
  `lawful_crossing_promotes`.
- `ActorTraceSpecimen`: `evidence_is_attributed` (inversion),
  `actor_trace_hop_does_not_transfer_standing`,
  `transfer_rule_is_directional`, `truncated_trace_no_reliance`.
- `LocalBoundaryPressure`: `weak_merge_accepts` +
  `merge_admissible_refuses` + `weakened_merge_allows_exposure_violation`,
  packaged as `weak_merge_is_not_merge`; `mergeAdmissible_weakens`
  (the weakening is genuine). Names `MergeAdmissible.left_sound` as the
  load-bearing field by construction.
- `SpendabilitySpecimen`: `eligibility_is_contractible` (validity duplicates
  freely) against the linear gate — `eligibility_does_not_mint_capacity`,
  `duplicated_eligibility_buys_nothing`, `no_eligibility_no_spend`
  (required, never payment), `deposit_without_admission_refused`,
  `replay_refused` (`[A] ⊬ A ⊗ A`), `wf_conserves` (inductive
  well-formedness; the count is conserved and that is ALL a green ledger
  says — conserved ≠ safe, effects opaque by construction). Fork residue:
  `revoked_fork_blocks_future_spend`, `revocation_does_not_unwind_effects`,
  `revocation_does_not_refund`, `residue_not_erased` (`revoke` is a real
  ledger function proved unable to reach the effect log — revoked ≠
  unwound). Gate design note: the amount bound is `all`-quantified over
  records carrying the drawn id, so conservation cannot be dodged by
  shadow records.
- `CustodyFreshnessSpecimen`: lawful evaluator (`freshAt`, producer clock
  only) vs the NAMED tempting evaluator (`freshByCustody`, "recently
  checked somewhere") — `custody_time_does_not_launder_observation_time`,
  `hop_does_not_refresh`, `absent_producer_clock_never_fresh`, and two
  inhabited separation witnesses (`custody_recency_is_not_freshness`,
  `custody_cannot_substitute_for_producer_clock`). Fresh-here ≠ fresh-there,
  with the wrong evaluator refuted by countermodel rather than omitted.
- `TemporalBasis`: `fresh_requires` (inversion — a `fresh` verdict
  certifies live source + admitted clock witness + declared window +
  present authority timestamp + tolerable uncertainty + window
  arithmetic; nothing else produces `fresh`), with corollaries per
  refusal surface: `stale_evidence_cannot_derive_fresh_claim`,
  `clock_cannot_testify_blocks_time_claim`,
  `missing_authority_time_no_fresh_claim`,
  `uncertainty_exceeding_window_not_fresh`, `undeclared_window_not_fresh`.
  minted ≠ observed: `generated_at_does_not_refresh_observation` (verdict
  invariant in `generatedAt`) + tempting evaluator `freshByGeneration`
  refuted by `repackaging_is_not_freshness`. elapsed ≠ revived:
  `retired_source_cannot_become_live_by_time_passing` (quantified over ALL
  evaluation times). silence ≠ recovery:
  `silence_does_not_establish_clear`,
  `stale_to_live_requires_fresh_admissible_basis`. existed ≠ fresh:
  `timestamped_existence_is_not_current_freshness`. late ≠ timely:
  `late_success_is_not_timely_success` (one report, completed AND
  deadline-missed), `incomplete_step_meets_no_deadline`. two clocks ≠ an
  order: `cross_basis_ordering_not_established`,
  `no_authority_time_no_ordering`. No `GlobalTrustedTime` — every verdict
  Profile-indexed (fence, not marker theorem).
- `ScopedCertification`: `establishes_requires_admitted_certifier` +
  `canCertify_inversion` (no third door: direct rule or one delegation hop
  from a directly-ruled donor), `certification_class_confinement`,
  `certification_scope_confinement`,
  `certification_not_transitive_without_rule` (delegation does not compose
  for free; two-hop chain refused in the `#eval` specimen),
  `self_certification_does_not_establish_authority`,
  `revoked_certifier_cannot_certify`,
  `filed_challenge_alone_does_not_block_reliance` +
  `admitted_challenge_blocks_reliance` (filed ≠ admitted; anti-DoS and
  anti-priesthood at once), `challenge_is_not_revocation` +
  `revocation_is_not_challenge` (inhabited separation witnesses, not
  vacuous invariance). Universal authority is unrepresentable — a
  documented fence, not a marker theorem; the bootstrap ("this profile is
  rightly active here") is explicitly not formalized. Sibling seams cited,
  not re-proved: bridge crossing (`BridgeCustomsSpecimen`), transport
  custody (`WLPAppendAckSpecimen`), witness-source admission
  (`StandingProfileSpecimen`/`RRPProfileSpecimen`), temporal validity
  (`Freshness`/`DeferredWitness`).

## The v9 non-claims (binding on release notes)

- **Not a unified dynamic calculus.** No global `Admissible` judgment; hops
  do not compose for free; each carries its own static witness. The dynamic
  layer is ANNEX, outside the 1.0 compatibility claim.
- **Not process semantics or runtime authority.** No scheduler, no
  concurrency model, no effect executor.
- **The specimen laws do not testify for runtime compliance.** v9 contains
  candidate formal laws for the Standing / WLP / bridge / actor-trace /
  local-boundary seams, written formalization-first. **They do not testify
  for RRP or any runtime's compliance by themselves.** Citation/adoption
  identifies the intended contract; conformance requires an explicit mapping
  plus runtime evidence or a refinement proof. Lean custody promotion is a
  separate review; none of these reviews is permission to begin the formal
  work. No vibes-based canonization.
- **The profile specimen is not the RRP implementation.** No canonical JSON,
  no SHA-256, no parser, no transport, no bridge custody (the bridge
  specimen's verifier is a stipulated flag; the RRP placeholder verifier is
  itself marked unsafe for production custody). It pins the semantics the
  Python/Rust checkers are supposed to have; the bridge from theorem to
  binary behavior is not built and is not claimed.
- **Receipt-level obstruction granularity is not modeled at decision level.**
  The specimen's `decision` collapses evidence failures to
  `claimNotEstablished`; the ABI's receipt-level codes appear as
  derivation-level refusal theorems.
- **`DynamicTrace` (production side) and `ActorTraceSpecimen` (consumption
  side) are separate seams.** The specimen pins what a trace may be spent on
  as standing evidence; `DynamicTrace` attributes hops. Connecting them is
  a future bridge theorem and its own promotion decision — v9 does not
  identify them.
- **`LocalBoundaryPressure` names one load-bearing field; it does not prove
  `MergeAdmissible` complete.** The five bad cases remain paper-shaped.
- **`ProofTheory` remains fenced.** Its "admissible" is literal Gentzen
  admissibility; no governance coupling.

## Gates (re-run 2026-07-09, exit codes observed)

| Gate | Result |
| --- | --- |
| `lake build` (default: AdmissibilityCustodyAnnex, Witnessed, BoundedCalculi, CustodyIndexedSequents, ProofTheory) | PASS |
| `lake build LeanProofs AdmissibilityMathlibIslands` (full aggregate + heavy island, 8335 jobs) | PASS |
| `lake build LeanProofs.Admissibility.RRPProfileSpecimen` (unwired candidate, direct) | PASS |
| Direct builds of the nine sibling specimens (`StandingProfileSpecimen`, `WLPAppendAckSpecimen`, `BridgeCustomsSpecimen`, `ActorTraceSpecimen`, `LocalBoundaryPressure`, `ScopedCertification`, `SpendabilitySpecimen`, `CustodyFreshnessSpecimen`, `TemporalBasis`) | PASS |
| `scripts/audit-axioms.sh` | PASS (23 signature, 8 specimen, 0 forbidden/unclassified) |
| `scripts/audit-native-decide.sh` | PASS (6 occurrences, all allowed finite-witness) |
| `scripts/check-custody-classes.sh` | PASS (58 files; counts match README) |
| `scripts/check-mathlib-pin.sh` | PASS |
| `scripts/check-witnessed-footprint.sh` | PASS (12 receipts within attested footprint) |
| `scripts/check-mathlib-free-targets.sh` | PASS (33-module closure Mathlib-free; negative-tested against the heavy island) |

## Open decisions flagged to operator (not blockers, not silently resolved)

1. ~~CI coverage narrowed by the default-target change~~ — **RESOLVED
   2026-07-09 (operator-directed):** explicit
   `lake build LeanProofs AdmissibilityMathlibIslands` CI step plus the
   repo audit scripts added to `lean_action_ci.yml`. Pre-split CI built the
   root aggregate via the old default targets, so this restores known cost.
2. ~~GPT-Pro roadmap L3–L7 not in this release~~ — **RESOLVED 2026-07-09
   (operator-directed, formalization-leads-implementation):** all five
   landed as UNRATIFIED-CANDIDATE specimen laws (L7's operator gate was
   opened explicitly). Promotion conditions are in each file header; none
   testify for runtime compliance until cited.
3. ~~AG/NQ crosswalk docs (L0 siblings) not written~~ — **RESOLVED
   2026-07-09 (operator-directed):** `docs/AG-TRANSITION-KERNEL-CROSSWALK.md`
   and `docs/NQ-NIGHTSHIFT-CROSSWALK.md`, written against live-repo doctrine
   surveys (not memory). Both defer to the consumer-side authorities that
   already exist (`transition-kernel/docs/LEAN_OBLIGATIONS.md`; NQ's
   `ROADMAP_EXPECTATIONS_FROM_LEAN_KERNEL.md` pinning discipline) and record
   folklore corrections where remembered doctrine phrases are not verbatim
   in the live docs (notably: "operator ack is not standing" is not AG
   doctrine — AG requires an `operator_approved` latch; the Lean specimen
   theorem is compatible but must be cited with that scoping).

## Scratch-steering promotion paths (named, deliberately not executed in v9)

The transition-kernel obligation ledger cites five SCRATCH modules as
candidate obligations (`NoFreeStandingReadout`, `TemporalCustody`,
`ExecutionRevalidation`, `MultiConsumerAdoption`, `NoFreeContinuation`).
That use is lawful under its own discipline (unratified fragment →
candidate obligation → mechanism + hostile specimen → observed
correspondence → ratification) and under this repo's ("scratch may inform,
not testify"). What would make heavier reliance lawful, per module:

1. Runtime ledger marks the row CORRESPONDS against **named theorems**
   (not file vibes), with its hostile specimen receipt.
2. This repo moves the module `Scratch/` → `Admissibility/` as
   UNRATIFIED-CANDIDATE (namespace + custody header + registry counts —
   a real churn, which is why it is not done hours before a mint).
3. ANNEX on the DeferredWitness precedent once the citation is live.

Not executed in v9: the moves would churn namespaces the runtime ledger
currently points at, mid-release. Named here so the next session ratifies
lazily instead of rediscovering. (The related tier drift — NQ's roadmap
tagging `ProjectionLaundering` scratch while it is UNRATIFIED-CANDIDATE
here — is recorded in the NQ crosswalk; the fix belongs on NQ's side.)

## Mint checklist (operator)

1. Review + commit this prep (operator drives git).
2. `git tag v9.0.0` on the prep commit.
3. Create the GitHub release (this mints the Zenodo version DOI).
4. Verify the Zenodo landing page shows the v9 title/description
   (CITATION.cff drives it; the v8 stale-title scar is the reason to check).
5. After-action doc sweep (Lean Admissibility README / WHAT-THIS-PROVES /
   PAPER-MAP / papers README) stays deferred per the papers-repo discipline
   ("after paper ships"), not release-gated.
