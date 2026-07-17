# RRP ↔ Lean Crosswalk

**Status: docs-only wiring (2026-07-09).** This file maps RRP doctrine — the
receipt-indexed admissibility gate prototype (`~/git/rrp`: Python reference
checker, Rust parity checker, corpus) — to existing Lean objects in this repo.
It changes no Lean files, no imports, no custody classes. It exists so RRP
docs and future checker work can cite the right Lean object without promoting
the wrong one.

**v13 correction:** custody now distinguishes exact stable roots, terminal
public evidence, and skunkworks incubation. This reclassification changes no
runtime-correspondence claim. See
[`V13-MIGRATION-LEDGER.md`](V13-MIGRATION-LEDGER.md).

**Citation discipline.** Custody class is part of the citation:

- **Stable surface** — compatibility-bearing exact-root closure.
- **Public evidence** — finished and citable, but not a compatibility promise.
- **Skunkworks** — incubation; never testifies for a runtime.

None of these theorems prove anything about the Python or Rust checkers.
They pin the semantics the checkers are supposed to have. The bridge from
"Lean theorem" to "this binary derives the right verdict" is not built, and
this file does not pretend it is.

## Doctrine rows

| RRP doctrine | Lean witness | Module | Custody |
| --- | --- | --- | --- |
| Receipt presence is not admissibility | `no_basis_never_authorized` (presence of a claim is not an admissible basis); at derivation level, `mem_deriveClaims` (every claim needs an *admitting* rule, not just a receipt) | `Admissibility/Authority.lean`; `Admissibility/RRPProfileSpecimen.lean` | stable [1.0]; public evidence |
| Advisory basis never authorizes | `advisory_basis_never_authorized` | `Admissibility/Authority.lean` | PUBLIC-SHIPPED [1.0] |
| All-green authority: basis ∧ precedence ∧ standing | `authorized_iff_all_green`; composed through derivations by `decide_authorized_requires_all_green` | `Admissibility/Authority.lean`; `Admissibility/Derivation.lean` | PUBLIC-SHIPPED [1.0] |
| Revoked basis cannot authorize | `revoked_basis_never_authorized`; lifted to execution as `revoked_basis_cannot_be_authorized_step` | `Admissibility/Derivation.lean`; `Admissibility/Execution.lean` | PUBLIC-SHIPPED [1.0] |
| Revoked standing cannot authorize | `revoked_standing_never_authorized`; `revoked_standing_cannot_be_authorized_step` | `Admissibility/Derivation.lean`; `Admissibility/Execution.lean` | PUBLIC-SHIPPED [1.0] |
| Execution requires BOTH mutation-side standing and claim-side authority | `AuthorizedStep` (no constructor without both proofs); `authorized_step_requires_authority` | `Admissibility/Execution.lean` | PUBLIC-SHIPPED [1.0] |
| Stale evidence is not fresh | `expired_not_fresh` (also `not_yet_valid_not_fresh`, `incoherent_not_fresh`, `divergence_excessive_not_fresh`) | `Admissibility/Freshness.lean` | PUBLIC-SHIPPED [1.0] |
| Deferred witness: pending is not admissible | `pending_not_admissible`, `lapsed_not_admissible`, `refused_not_admissible` — only `completed` is admissible | `Admissibility/DeferredWitness.lean` | public evidence |
| Late evidence cannot create prior standing | `no_retroactive_standing`, `necromancy_rejected`, `stale_evidence_rejected`, `mutated_terms_rejected` | `Admissibility/DeferredWitness.lean` | public evidence |
| Classifier agrees with spec (obstruction ↔ refusal) | `firstViolation_none_iff_lawful`, `firstViolation_isSome_iff_not_lawful` (proved 2026-07-09) | `Admissibility/DeferredWitness.lean` | public evidence |
| Downstream proposal cannot bind when upstream claim basis refused | `downstream_proposal_cannot_bind_when_claim_basis_refused`; generic engine `refusal_composes_two_hop`, `refusal_propagates_transitively` | historical public path `Admissibility/RefusalPropagation.lean` | skunkworks; reconnaissance only |

## Checker-behavior rows (RRP obstruction ABI)

The RRP local obstruction catalog (`schemas/obstructions.v1.json`) refuses at
receipt, claim, effect, profile, request, transport, and process boundaries.
The Lean neighbors:

| Checker behavior | Lean witness | Module | Custody |
| --- | --- | --- | --- |
| `MissingReceipt` — no receipt, no claim | `missing_receipt_no_claim` (empty form), `missing_receipt_kind_no_claim` (kind form) | `Admissibility/RRPProfileSpecimen.lean` | public evidence |
| `CannotTestify` — receipt present, witness not admitted | `cannot_testify_not_admitted` / `cannot_testify_no_claim` | `Admissibility/RRPProfileSpecimen.lean` | public evidence |
| `StaleWitness` — evidence outside freshness window | `stale_not_admitted` / `stale_receipt_no_claim`; abstract ancestor `expired_not_fresh` | `Admissibility/RRPProfileSpecimen.lean`; `Admissibility/Freshness.lean` | public evidence; stable [1.0] |
| Revoked basis refuses | `revoked_not_admitted` / `revoked_basis_no_claim`; abstract ancestors in `Derivation`/`Execution` (rows above) | `Admissibility/RRPProfileSpecimen.lean` | public evidence |
| `ClaimNotEstablished` / effect rules require claims | `effect_requires_claim`, `no_required_claim_no_permit`, `no_evidence_no_permit` | `Admissibility/RRPProfileSpecimen.lean` | public evidence |
| `profile_digest` is authority identity; `profile_id` is metadata | `profile_id_only_no_decision`, `digest_mismatch_refused` | `Admissibility/RRPProfileSpecimen.lean` | public evidence |
| Requester cannot witness its own standing | `self_authorization_refused` | `Admissibility/RRPProfileSpecimen.lean` | public evidence |
| Unknown JSON keys fail closed | **Not formalized.** Parser/corpus property; belongs to the checker test suite, not Lean (canonical-JSON is deliberately outside the specimen). | — | — |
| Canonical JSON / digest computation | **Not formalized** (deliberate — `Profile.digest` is a symbolic stand-in; collision resistance is a crypto assumption, not a theorem here). | — | — |
| Decision is a discriminated union, not a boolean | `Decision` inductive (`permit`/`refusal`), specimen-level only | `Admissibility/RRPProfileSpecimen.lean` | public evidence |
| Standing sources: schedule / operator ack / model output are not standing | `schedule_is_not_standing`, `operator_ack_is_not_standing`, `model_output_is_not_standing`, `revoked_basis_no_standing`; scoping at the gate: `wrong_actor_not_permitted`, `wrong_project_not_permitted` | `Admissibility/StandingProfileSpecimen.lean` | public evidence |
| Bridge: source permit is not target permit | `source_permit_alone_no_target_effect`, `bridge_claim_cannot_widen_scope`, `target_profile_mismatch_no_local_claim`, `source_refusal_no_local_claim` (pairwise; verifier stipulated, no PKI). Doctrine ancestors: v7 artifact-authority-profile work, `Witnessed` no-free-lift line (`no_free_lift`, `paid_lift_sound`). | `Admissibility/BridgeCustomsSpecimen.lean`; `Witnessed/` | public evidence; stable calculus |
| Transport acks are not permits (WLP-shape) | `append_ack_alone_no_authorized_effect`, `append_ack_supports_custody_but_not_authority`, `more_transport_evidence_never_authorizes`. Abstract neighbor: `advisory_basis_never_authorized`. | `Admissibility/WLPAppendAckSpecimen.lean` | public evidence |
| Actor-indexed traces / hop cannot transfer standing | `actor_trace_hop_does_not_transfer_standing`, `transfer_rule_is_directional`, `truncated_trace_no_reliance`. Production-side neighbor: `DynamicTrace.traceHopsByActor_actor` (separate stable family); the two seams are NOT identified. | `Admissibility/ActorTraceSpecimen.lean` | public evidence |

## What this crosswalk does NOT license

- It does not turn the specimen laws into RRP conformance evidence. Six are
  terminal public evidence (`RRPProfileSpecimen`, `StandingProfileSpecimen`,
  `WLPAppendAckSpecimen`, `BridgeCustomsSpecimen`, `ActorTraceSpecimen`, and
  `ScopedCertification`); `LocalBoundaryPressure` remains staged for
  skunkworks. Citation/adoption identifies the intended contract; conformance
  requires an explicit mapping plus runtime evidence or a refinement proof.
- It does not claim the abstract kernel instantiates the RRP artifact ABI.
  `Derivation.BasisDerivation` is abstract over derivation functions; deciding
  what `requiredFor`/`witnesses` mean inside the public authority kernel is a
  promotion boundary (see `SEMANTIC_WIRING_AUDIT.md`), not a refactor.
- It does not unify obstruction taxonomies. `AuthorityVerdict`, `Freshness`
  verdicts, `DeferredWitness.firstViolation`, and the specimen's `Obstruction`
  are separate classifiers by design; the repeated pattern is "classifier +
  one negative theorem per failing dimension," not one universal `Refusal`.

Provenance: GPT-Pro Lean-repo audit (2026-07-08, `~/git/rrp-notes/gptpro-lean`),
L0 slice; written against repo state at v8.0.0 + codex-derived work.
