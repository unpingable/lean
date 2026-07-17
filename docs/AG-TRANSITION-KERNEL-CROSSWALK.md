# AG / Transition-Kernel ↔ Lean Crosswalk

**Status: docs-only wiring (2026-07-09).** This file maps the agent-governor
constellation's runtime doctrine — `~/git/agent_gov` (AG, the governor),
`~/git/transition-kernel` (the governed-transition office, Rust),
`~/git/linearaccountant` (LA, the spendability authority),
`~/git/governor-atlas` — to Lean objects in this repo. It changes no Lean
files, no imports, no custody classes. All runtime quotes below were taken
from the live repos on 2026-07-09, not from cached memory.

**v13 correction:** custody labels below now use stable API, terminal public
evidence, or skunkworks-bound/historical. Theorems did not acquire runtime
correspondence through reclassification. See
[`V13-MIGRATION-LEDGER.md`](V13-MIGRATION-LEDGER.md).

**This crosswalk is the INVERSE view of an existing runtime ledger.** The
transition-kernel already maintains the authoritative Rust→Lean obligation
ledger at `~/git/transition-kernel/docs/LEAN_OBLIGATIONS.md` (with
`CORRESPONDENCE.md` and `NON_CORRESPONDENCE.md`), keyed by Lean module and
custody class, with dispositions `UNREALIZED / PARTIAL / CORRESPONDS`. That
ledger owns the correspondence *claims*; this file is the Lean-side index
into it plus doctrine rows the ledger does not cover. Where they disagree,
the runtime ledger's disposition wins for runtime claims and this repo's
custody markers win for Lean claims.

**The fence, quoted from the runtime side because it says it best:**

> "The forbidden inversion — `Lean theorem → Rust copies a theorem-shaped
> API → 'validated'` — is ceremonial self-affirmation with types and is not
> permitted. A green build here is **never** evidence that a Lean theorem
> holds." — `transition-kernel/docs/LEAN_OBLIGATIONS.md`

Symmetrically: no theorem in this repo is evidence that the Rust kernel
behaves. Citation discipline as in `RRP-LEAN-CROSSWALK.md`: custody role is
part of the citation. **Skunkworks and historical fossils never testify for a
runtime**; such rows are reconnaissance only.

## Doctrine rows

| Runtime doctrine (verbatim, cited) | Lean witness | Module | Custody |
| --- | --- | --- | --- |
| "The admission candidate carries two separately-constructed proofs with no coercion between them" (`transition-kernel/docs/CORRESPONDENCE.md`); "There is deliberately no `From<WriteStanding>` — read-standing cannot become write-standing for free" (`src/transition_core.rs`) | `AuthorizedStep` (no constructor without both proofs); `authorized_step_requires_authority`; the no-coercion wall is `NoFreeStandingBridge` | `Admissibility/Execution.lean`; `Admissibility/NoFreeStandingBridge.lean` | stable [1.0]; public evidence |
| "**Candidate ≠ authority.** … `AuthorizedTransition` is unconstructable here" (`transition-kernel/CONTRACT.md`, Invariant 2) | Same unconstructability pattern: `AuthorizedStep` exists only with both proofs; downstream binding wall `downstream_proposal_cannot_bind_when_claim_basis_refused` | `Admissibility/Execution.lean`; historical public path `Admissibility/RefusalPropagation.lean` | stable [1.0]; skunkworks (reconnaissance) |
| "'readable/present' yields no standing" (`LEAN_OBLIGATIONS.md`); "**It does not establish standing.** Standing is fetched and verified from the `standing` office" (`transition-kernel/NON_CLAIMS.md`) | Runtime ledger row cites `NoFreeStandingReadout` — skunkworks reconnaissance. Public neighbors: `revoked_standing_never_authorized`, `no_standing_never_authorized`; derivation-side `StandingProfileSpecimen` | v12 `Scratch/NoFreeStandingReadout.lean`; `Admissibility/Derivation.lean` + `Authority.lean`; `Admissibility/StandingProfileSpecimen.lean` | skunkworks; stable [1.0]; public evidence |
| "**Possession is not permission.** Having evidence does not entitle you to rely on it" (`agent_gov/docs/SHARED_INVARIANTS.md`) | `no_basis_never_authorized` / `advisory_basis_never_authorized` (presence and advice are not authority); `mem_deriveClaims` (no claim without an admitting rule) | `Admissibility/Authority.lean`; `Admissibility/RRPProfileSpecimen.lean` | stable [1.0]; public evidence |
| "**Standing**: grants scoped to action + target; a deploy grant doesn't authorize reads … Scope is not inherited or broadened without new grant" (`agent_gov/docs/SHARED_INVARIANTS.md` §7, `FAILURE_CROSSWALK.md`) | `certification_class_confinement` + `certification_scope_confinement` (force confined to admitted class × scope); `wrong_actor_not_permitted` / `wrong_project_not_permitted` | `Admissibility/ScopedCertification.lean`; `Admissibility/StandingProfileSpecimen.lean` | public evidence |
| "**No self-approval.** An actor's output never greens its own gate. … A written 'approved' confers nothing" (`agent_gov/docs/NON_GRANTS.md` §1–2) | `self_certification_does_not_establish_authority`; `self_authorization_refused` | `Admissibility/ScopedCertification.lean`; `Admissibility/RRPProfileSpecimen.lean` | public evidence |
| "**Validity is contractible; spendability is linear.** `valid(x) ∧ valid(x) ≡ valid(x)`, but `[A] ⊬ A ⊗ A` … Each consumption event id consumes at most once; replays are refused" (`linearaccountant/README.md`) | Runtime ledger row: `ContractionHinge` ("CORRESPONDS (operational)" per `LEAN_OBLIGATIONS.md` — LA is the sole authoritative burn, replay refuses via `AlreadyConsumed`). LA also keeps its own Lean twin (`linearaccountant/verification/Ledger.lean` — conservation + replay refusal), which is LA's artifact, not this repo's. | `Admissibility/ContractionHinge.lean` | public evidence |
| "Validation may mint *eligibility*. Only the accountant may mint or consume *capacity*. Eligibility is a request, not payment" (`linearaccountant/README.md`); "Deposit must cite a budget admission reference … LA does not evaluate authorization" (`docs/working/decisions/budget-admission-forcing-case.md`) | The split as law: `eligibility_is_contractible` vs the linear gate; `eligibility_does_not_mint_capacity`, `duplicated_eligibility_buys_nothing`, `no_eligibility_no_spend` (required, never payment); `deposit_without_admission_refused`; `replay_refused`; `wf_conserves` (the count is conserved — and that is ALL a green ledger says). Doctrine ancestors: `Witnessed` no-free-lift; `effect_requires_claim`. | `Admissibility/SpendabilitySpecimen.lean`; `Witnessed/` | public evidence; stable calculus |
| "`RevokedFork ↛ UnwoundForkEffects` … Revocation is a flag that blocks *future* draws; it makes no claim about effects that already crossed the membrane" (`linearaccountant/docs/working/revoked-fork-residue-hazard.md`); "A green consume receipt means the count was conserved — not that the effect was safe" | The residue laws: `revoked_fork_blocks_future_spend` (future refused), `revocation_does_not_unwind_effects` + `revocation_does_not_refund` (history and counts untouched), `residue_not_erased`. Kernel ancestors: `revoked_basis_cannot_be_authorized_step` / `revoked_standing_cannot_be_authorized_step`; dynamic `revoked_*_blocks_dynamic_step`. The hazard doc's v12 `Scratch/QuorumResidueCoupling.lean` reference is skunkworks-bound reconnaissance. | `Admissibility/SpendabilitySpecimen.lean`; `Admissibility/Execution.lean`; `Admissibility/DynamicTrace.lean` | public evidence; stable [1.0]; separate stable family |
| "freshness re-checked at the boundary, not inherited from citation; refuse stale-at-use … `ExecutionRevalidation` rechecks Standing liveness + freshness at the *execution* clock" (`LEAN_OBLIGATIONS.md`, `CORRESPONDENCE.md`) | The old Scratch rows are historical/skunkworks reconnaissance. Public neighbors: `BoundedCalculi.TemporalCustody`, `expired_not_fresh`, and the discharge-at-current-clock family `stale_observation_cannot_discharge_current_obligation` (+ five per-mode theorems). | v12 `Scratch/ExecutionRevalidation.lean`; `BoundedCalculi/TemporalCustody.lean`; `Admissibility/Freshness.lean`; `Admissibility/FreshnessDynamicTrace.lean` | skunkworks; public Bounded family; stable [1.0]; separate stable family |
| "**No spend past the standing horizon.** A spend attempt whose standing observation lapsed past its freshness bound between observation and exercise time is refused, even when the standing was valid at observation" (`agent_gov/docs/NON_GRANTS.md` §7) | The two-clock shape: `stale_observation_cannot_discharge_current_obligation` (fresh-at-observation is not fresh-at-discharge); `stale_evidence_rejected` | `Admissibility/FreshnessDynamicTrace.lean`; `Admissibility/DeferredWitness.lean` | separate stable family; public evidence |
| "an amend-policy step requires a pre-state validation token; self-grant unconstructible" (`LEAN_OBLIGATIONS.md`, row `AmendmentFragment`) | `AmendmentFragment` (the ledger's named target); store-isolation floor: `amend_policy_targets_policy_store` + the `authorized_*_does_not_amend_policy` family; dynamic form `non_amend_trace_preserves_policy` | `Admissibility/AmendmentFragment.lean`; `Admissibility/StateTransition.lean` + `Execution.lean`; `Admissibility/DynamicTrace.lean` | public evidence; stable [1.0]; separate stable family |
| "Refusal here is a product surface, not an error state: each organ refuses with a **typed reason on a receipt** … at a named seam" (`agent_gov/docs/REFUSAL_GALLERY.md`); closed 12-kind refusal taxonomy (`transition-kernel/CONTRACT.md`) | The repeated Lean pattern is the same shape — a classifier plus one negative theorem per failing dimension (`AuthorityVerdict`, `Freshness` verdicts, `firstViolation` + its reflection lemma `firstViolation_none_iff_lawful`, specimen `Obstruction` types) — **deliberately NOT unified into one `Refusal` type**, matching the runtime's per-seam taxonomies. | `Admissibility/Authority.lean`, `Freshness.lean`, `DeferredWitness.lean`, `RRPProfileSpecimen.lean` | mixed (see modules) |

## Folklore corrections (memory vs live doctrine)

The GPT-Pro audit and this repo's working notes carry several shorthand
phrases. The 2026-07-09 survey found they are **not verbatim** in the live
runtime docs, and one is misleading. Recorded here so the shorthand does not
harden into fake citations:

- **"Standing output alone does not authorize effects"** — not stated. Live
  forms: "'readable/present' yields no standing" (`LEAN_OBLIGATIONS.md`) and
  "It does not establish standing" (`NON_CLAIMS.md`).
- **"Claim-side alone is not enough / mutation-side alone is not enough"** —
  not stated. Live forms: "Candidate ≠ authority" and `AdmissionCandidate::new`
  "requires *both* proofs by value" (`CONTRACT.md`, `CORRESPONDENCE.md`).
- **"LA burn is not admission"** — not stated. Live forms: "Deposit must cite
  a budget admission reference … LA does not evaluate authorization" and "a
  green consume receipt means the count was conserved — not that the effect
  was safe."
- **"Proposal packet is not admission"** — not stated; the live docs state the
  *inverse order* (the packet is emitted after admission + consume and "is
  not a write"). Verbatim siblings that DO exist: "Verification is not
  admission," "Testimony is not admission," "Branch existence is not
  admission," "Schema-valid is not admission."
- **"Operator ack is not standing"** — NOT AG doctrine, and would partly
  contradict it: AG *requires* an explicit `operator_approved: true` latch for
  queue admission (`NON_GRANTS.md` §2). AG's actual non-grants are "no
  self-approval" and "no authority from prose." The compatible Lean-side law
  is `StandingProfileSpecimen.operator_ack_is_not_standing`, which says an
  operator ack does not *derive the standing claim* — an ack can be a
  necessary admission latch without being standing. Cite it only with that
  scoping.

## What this crosswalk does NOT license

- It does not import the runtime ledger's dispositions as Lean facts, nor
  export Lean custody as runtime validation (both fences quoted above).
- It does not turn skunkworks or historical modules referenced by the runtime
  ledger (`NoFreeStandingReadout`, the old Scratch `TemporalCustody`,
  `ExecutionRevalidation`, `MultiConsumerAdoption`, `NoFreeContinuation`) into
  public testimony. They remain reconnaissance obligations.
- It does not pin line numbers. `LEAN_OBLIGATIONS.md` carries Lean `file:line`
  references against a hand-managed checkout, some marked uncommitted; this
  file cites module + theorem names only.
- It does not identify `SpendabilitySpecimen` with LA's own Lean twin
  (`linearaccountant/verification/Ledger.lean`) — the specimen pins the
  laws formalization-first; LA's twin verifies LA's implementation. Two
  artifacts, two custodies, no free bridge between them.

Provenance: GPT-Pro Lean-repo audit L0 (2026-07-08, `~/git/rrp-notes/gptpro-lean`);
live-repo doctrine survey 2026-07-09. Note: the `~/git/scheduler` path in
older notes does not exist — the transition kernel is a standalone repo at
`~/git/transition-kernel`.
