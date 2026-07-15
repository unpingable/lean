# NQ / Nightshift ↔ Lean Crosswalk

**Status: docs-only wiring (2026-07-09).** This file maps NQ (`~/git/nq-root/nq`,
the claim-admissibility engine: "cross-examines observability, refuses to
launder observations into authority") and Nightshift (`~/git/nightshift`, the
non-actuating reconciling daemon; `nightshiftd` lives at
`~/git/nightshift/crates/nightshiftd/` — the `~/git/scheduler` path in older
notes does not exist) to Lean objects in this repo. It changes no Lean files,
no imports, no custody classes. All runtime quotes were taken from the live
repos on 2026-07-09, not from cached memory.

**NQ already governs its own side of this seam.** The authoritative
consumer-side document is
`nq/docs/theory/ROADMAP_EXPECTATIONS_FROM_LEAN_KERNEL.md`, whose headline is
the right fence for both directions:

> "The Lean kernel does not tell NQ to become more powerful. It tells NQ to
> become more exact about what its testimony can and cannot support."

That file also defines NQ's **pinning discipline**: `[1.0]` modules may pin
testimony shape; `[annex]` modules may be *cited as evidence* but never pin a
wire field; it currently says scratch "must not steer NQ implementation unless
they graduate." Under this repo's 2026-07-14 development-order policy, that
last sentence remains a production-custody rule: Scratch may precede and inform
prototype exploration, but it may not normatively steer or pin production.
That rule does not block Scratch theorem development. Candidate or promoted
formal contracts may lead code under their own custody rules, and no tier may
claim runtime conformance without a mapping plus runtime evidence or refinement.
This repo's custody classes map onto it as: PUBLIC-SHIPPED → `[1.0]`,
ANNEX → `[annex]`, and both UNRATIFIED-CANDIDATE and SCRATCH fall under the
non-pinning rule (candidates are *named*, which scratch is not, but neither
may testify). NQ's tier tags predate this repo's UNRATIFIED-CANDIDATE
class; one known drift is recorded below.

## Doctrine rows

| Runtime doctrine (verbatim, cited) | Lean witness | Module | Custody |
| --- | --- | --- | --- |
| "**Present tense requires a live basis. History may survive; active truth may not be faked. Retirement is explicit, not inferred from silence.**" (`nq/docs/working/gaps/EVIDENCE_RETIREMENT_GAP.md`) | The lapse path: `statusOf` sends an expired, uncompleted window to `lapsed`, and `pending_not_admissible` / `lapsed_not_admissible` / `refused_not_admissible` — only `completed` is admissible. This is the module NQ's EVIDENCE_RETIREMENT slice already cites as `[annex]` evidence (its promotion context, not a formalization gate). Classifier now theorem-backed: `firstViolation_none_iff_lawful` (2026-07-09). | `Admissibility/DeferredWitness.lean` | ANNEX |
| "Testimony exists but its `observed_at` is outside the freshness policy for this claim kind … Freshness is evaluated against `observed_at`, not `generated_at` or ingest time" (verdict `stale_testimony`, `nq/docs/operator/VERDICTS.md`) | `expired_not_fresh` (+ the four sibling `*_not_fresh` refusals); `stale_evidence_rejected`; derivation form `stale_receipt_no_claim` / `stale_not_admitted`; the observed/generated split itself: `generated_at_does_not_refresh_observation` + separation witness `repackaging_is_not_freshness` | `Admissibility/Freshness.lean`; `Admissibility/DeferredWitness.lean`; `Admissibility/RRPProfileSpecimen.lean`; `Admissibility/TemporalBasis.lean` | PUBLIC-SHIPPED [1.0]; ANNEX; UNRATIFIED-CANDIDATE ×2 |
| Basis-stale contract: transitions keyed to "the operator-declared freshness window" and an authority timestamp, never inferred cadence (`nq/docs/working/decisions/BASIS_STALE_CONTRACT.md`); "Retirement is explicit, not inferred from silence" + "loss of observability reduces confidence; it does not fabricate health" (`EVIDENCE_RETIREMENT_GAP.md`, `nq` README); `cannot_testify` is constitutional (`VERDICTS.md`) | The NQ-facing time-assurance specimen (NQ-T4 of the temporal track, written before NQ implements T0–T3): `fresh_requires` (a fresh verdict certifies the whole declared contract), `undeclared_window_not_fresh`, `missing_authority_time_no_fresh_claim` (collected_at is not authority unless admitted), `clock_cannot_testify_blocks_time_claim`, `uncertainty_exceeding_window_not_fresh`, `retired_source_cannot_become_live_by_time_passing`, `silence_does_not_establish_clear` + `stale_to_live_requires_fresh_admissible_basis`, `timestamped_existence_is_not_current_freshness`, `late_success_is_not_timely_success`, `cross_basis_ordering_not_established`. Typed `TemporalVerdict` (stale / cannotTestify / unknownAuthorityTime … are siblings, not string reasons). | `Admissibility/TemporalBasis.lean` | UNRATIFIED-CANDIDATE |
| "**Night Shift may consume NQ findings. It cannot upgrade custody into basis.** … **Freshness is not transitive across custody.** … If the producer clock is absent or incoherent, freshness is *unknown / cannot-assess* — never inferred" (`nightshift/docs/working/gaps/GAP-imported-basis-freshness.md`, `crates/nightshiftd/src/freshness.rs`) | The chain-shaped law itself: `custody_time_does_not_launder_observation_time` (verdict invariant under the custody chain), `hop_does_not_refresh`, `absent_producer_clock_never_fresh`, and the inhabited separation witnesses `custody_recency_is_not_freshness` / `custody_cannot_substitute_for_producer_clock` (the tempting "recently checked somewhere" evaluator is modeled and refuted by countermodel, not just omitted). Neighbors: crossing imports testimony under a cap, never basis (`source_permit_alone_no_target_effect`, `bridge_claim_cannot_widen_scope`); two-clock non-inheritance (`stale_observation_cannot_discharge_current_obligation`). | `Admissibility/CustodyFreshnessSpecimen.lean`; `Admissibility/BridgeCustomsSpecimen.lean`; `Admissibility/FreshnessDynamicTrace.lean` | UNRATIFIED-CANDIDATE; UNRATIFIED-CANDIDATE; ANNEX |
| "A relevant witness has explicitly declared the requested conclusion as outside its `cannot_testify` list … This is **constitutional** output, not error condition" (`nq/docs/operator/VERDICTS.md`); `cannot_testify` = "structural inability to observe (collector lacks standing)" (ROADMAP) | `cannot_testify_not_admitted` / `cannot_testify_no_claim` (a witness the rule does not admit contributes nothing — refusal, not error); the wall between predicate satisfaction and admissibility witness is `PredicateWitnessSeparation` | `Admissibility/RRPProfileSpecimen.lean`; `Admissibility/PredicateWitnessSeparation.lean` | UNRATIFIED-CANDIDATE; ANNEX |
| "Finding ≠ claim. Witnesses observe; they do not promote. Receipts attest; they do not authorize mutation." (`nq/docs/operator/REFUSAL_EXAMPLES.md`) | Observations are not claims: `mem_deriveClaims` (the only path from receipt to claim is an admitting rule); receipts attest without authorizing: `append_ack_supports_custody_but_not_authority`; mutation needs both proofs: `AuthorizedStep` | `Admissibility/RRPProfileSpecimen.lean`; `Admissibility/WLPAppendAckSpecimen.lean`; `Admissibility/Execution.lean` | UNRATIFIED-CANDIDATE; UNRATIFIED-CANDIDATE; PUBLIC-SHIPPED [1.0] |
| "a multi-witness finding's standing is not the sum of its component witnesses' standings. Agreement among witnesses is not automatically corroboration. … A finding is not more qualified than the composition rule that minted it" (ROADMAP, `WitnessInvariance` section) | `WitnessInvariance` — the module NQ's roadmap pins this against, on the `[1.0]` surface | `Admissibility/WitnessInvariance.lean` | PUBLIC-SHIPPED [1.0] |
| "`ok_to_proceed` is NOT an authorization summary" (`GAP-imported-basis-freshness.md`, sentinel test `b2_stale_imported_basis_sentinel_ok_to_proceed_is_not_authorization`); "Run-ledger events are NOT authority receipts … Night Shift does not manufacture authority by logging itself" (`crates/nightshiftd/src/ledger.rs`) | An advisory signal never authorizes: `advisory_basis_never_authorized`; logging/publication is custody evidence, not claim authority: `transport_evidence_mints_no_claims`, `more_transport_evidence_never_authorizes` | `Admissibility/Authority.lean`; `Admissibility/WLPAppendAckSpecimen.lean` | PUBLIC-SHIPPED [1.0]; UNRATIFIED-CANDIDATE |
| "A `ProposedAction` is a **description**, not an instruction NS can execute" (`crates/nightshiftd/src/proposed_action.rs`); "NQ findings are **evidence, not commands**" (`src/nq.rs`) | The downstream binding wall: `downstream_proposal_cannot_bind_when_claim_basis_refused`, `refused_blocks_binding`; effects require claims: `effect_requires_claim` / `no_required_claim_no_permit` | `Admissibility/RefusalPropagation.lean`; `Admissibility/RRPProfileSpecimen.lean` | ANNEX; UNRATIFIED-CANDIDATE |
| "`silence_present ≠ incident_absent`, `acked_silence ≠ acked_incident`, `no_new_evidence ≠ resolved`" (`crates/nightshiftd/src/posture_class.rs`) | Nightshift's own audit backlog already cross-references `ProjectionLaundering.lean` for the first inequation. NQ's roadmap tags it scratch — **tier drift: it is UNRATIFIED-CANDIDATE in this repo now** (named, still non-pinning). The absence-vs-refusal cut also lives in the runtime's own `insufficient_coverage` vs `cannot_testify` distinction; the ACK/NACK asymmetry ("missing ACK ≠ NACK") now has a fenced formal core in `Scratch/SignalAuthority.lean`, which may inform but not pin production. | `Admissibility/ProjectionLaundering.lean`; `Scratch/SignalAuthority.lean` | UNRATIFIED-CANDIDATE; SCRATCH |
| "**The 3am agent must not act on 11pm vibes.**" (capture→reconcile freeze, `nightshift/docs/working/gaps/GAP-deferred-run-split.md`); "**Deferred obligation is not deferred authorization.**" (`GAP-workflow-routing-boundary.md`) | Shape-neighbor, not vocabulary match (see absences): the one lawful deferral in Lean is `DeferredWitness` — deferred *completion* is licensed only by a grant witnessed **before** reliance (`no_retroactive_standing`, `necromancy_rejected`), and deferral licenses evidence arrival, never authorization. The runtime defers *obligations/runs* (freeze-then-reconcile), a different object with the same refusal grain: deferral never mints authority across the gap. | `Admissibility/DeferredWitness.lean` | ANNEX |
| "**Standing is necessary, not sufficient.** … Verification is not permission. Memory is not testimony." (`GAP-workflow-routing-boundary.md` keepers) | `authorized_iff_all_green` (standing is one conjunct of three, never sufficient alone); `no_standing_never_authorized` | `Admissibility/Authority.lean` | PUBLIC-SHIPPED [1.0] |
| Nightshift refusal surface: `NightShiftError` = `AgendaNotFound / InvalidAgenda / EvidenceSourceNotAllowed / AuthorityCeilingExceeded / PreflightBlocked / RunAlreadyCompleted / NqInadmissible` (`crates/nightshiftd/src/errors.rs`); NQ's closed 8-verdict set (`VERDICTS.md`) | Same shape as the Lean house pattern: per-seam classifier + one negative theorem per failing dimension, deliberately not unified (`AuthorityVerdict`, `Freshness` verdicts, `firstViolation` + reflection, specimen `Obstruction`s). `RunAlreadyCompleted` ("reconcile is one-shot") is contraction-shaped — Lean neighbor `ContractionHinge`. | multiple (see modules); `Admissibility/ContractionHinge.lean` | mixed; UNRATIFIED-CANDIDATE |

## Vocabulary absences (both directions, stated honestly)

- **Pending / lapsed / completed grant lifecycle, grant windows, "pending is
  not admissible"** — NOT stated in NQ/Nightshift runtime docs. That
  vocabulary is Lean-side (`DeferredWitness`). NQ's `basis_state` lifecycle
  (`live | stale | retired | invalidated | unknown`) is, per NQ's own roadmap,
  "*evidence lifecycle*, not verdict … The two vocabularies are deliberately
  different cuts; they should stay different." The DeferredWitness row above
  maps refusal *shape*, not vocabulary — do not sync the enums.
- **Backflow / necromancy naming** — zero occurrences in either runtime repo.
  The nearest runtime rules are custody non-transitivity of freshness and
  explicit evidence retirement. The Lean names stay Lean-side.
- **"Nightshift packet is not authority"** as a five-word sentence — not
  stated verbatim; the live forms are "`ProposedAction` is a description" and
  "Run-ledger events are NOT authority receipts."
- ~~Custody-clock non-transitivity not formalized~~ — closed 2026-07-09 by
  `CustodyFreshnessSpecimen` (UNRATIFIED-CANDIDATE; see row above). NQ's
  `basis_state` lifecycle remains deliberately unmirrored — the specimen
  models producer-clock evaluation, not NQ's evidence lifecycle.
- **NQ's basis-verdict vocabulary vs Lean's** — NQ's roadmap explicitly
  refuses an NQ-side "authorize/approve/safe" verb and refuses mirroring:
  NQ canon is "a *superset* of the Lean 14, not a mirror" (TaxonomyGraph
  section). This crosswalk respects both refusals.

## What this crosswalk does NOT license

- It does not let any Lean module pin an NQ wire field or doc concept — that
  right is reserved to `[1.0]` modules by NQ's own pinning discipline, and
  nothing here extends it.
- It does not promote `ProjectionLaundering` (named tier drift above is a
  bookkeeping fact, not a promotion), `DeferredWitness` beyond ANNEX, or any
  specimen law. Specimens do not testify for runtime compliance until cited
  by runtime artifacts under the DeferredWitness precedent.
- It does not unify the refusal taxonomies (NQ's 8 verdicts, Nightshift's
  error enum, the Lean classifiers) — all sides keep per-seam vocabularies
  on purpose.

Provenance: GPT-Pro Lean-repo audit L0 (2026-07-08, `~/git/rrp-notes/gptpro-lean`);
live-repo doctrine survey 2026-07-09. Companion NQ-side documents:
`nq/docs/theory/ROADMAP_EXPECTATIONS_FROM_LEAN_KERNEL.md` (consumer-side
authority on pinning) and
`nq/docs/working/WITNESSED_DERIVATION_CALCULUS_NQ_MAPPING.md` (NQ claim paths
↔ `Witnessed` theorems).
