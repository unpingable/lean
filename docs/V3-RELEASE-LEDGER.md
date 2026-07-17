# v3 Release Ledger — Bounded Lifecycle Calculi

> **Historical record.** Custody labels and paths below describe the v3 tree.
> The post-v12 v13 migration later classified this finished family under
> public stable/evidence roles without changing its mathematics. See
> [`V13-RELEASE-LEDGER.md`](V13-RELEASE-LEDGER.md).

**Release: v3.0.0 — Bounded Lifecycle Calculi** (*A Lean proof release for
custody-aware authority semantics*). Umbrella: Custody-Aware Authority
Semantics. Next campaign: Custody-Indexed Sequents (v3.x).

This ledger is the theorem inventory and proof-shape classification the v3 bar
requires (roadmap §10 slice L1, closed 2026-07-01). It records what exists and
what stage each artifact survived. The release/DOI act itself is the operator's.

## Custody decision (operator, 2026-07-01) — Option A executed

`ExecutionCustody`, `BootKernel`, and `CheckpointSettlement` were **promoted
Scratch → `BoundedCalculi/` ANNEX release surface**, with `MeasureAccounting`
extracted as a support module so the release surface imports no scratch
(import direction: ANNEX → Witnessed/ANNEX only; Scratch → ANNEX).

> These modules are release-surface bounded calculi, not a unified
> admissibility calculus and not imported into promoted kernels.

**Gate record (2026-07-01, receipts under `.governor/verify_receipts/`):**
full `lake build` green (8336 jobs); per-file typecheck PASS for all nine
family modules + support + sequent scratch; `audit-axioms.sh` /
`audit-native-decide.sh` / `check-mathlib-pin.sh` /
`check-witnessed-footprint.sh` all exit 0; zero `sorry`/`admit`/
`native_decide`; axiom footprints re-attested post-move (table below);
**`LeanProofs.lean` imports neither `BoundedCalculi` nor `Scratch`** (promoted
kernel/import boundary unchanged); the aggregate remains a compile marker.

**The v3 claim (ratified):** v3 completes the bounded lifecycle-calculi
FAMILY — many local judgments, each with positive rules and non-collapse
walls, **no master `Admissible`**, no default bridge transitivity. It does NOT
claim the family composes as an indexed sequent system (that is the v3.x
Custody-Indexed Sequents campaign / v4 Gentzen ambition, named below, not
claimed), and it does NOT claim custody-aware authority semantics as a whole
(runtime, actuators, and bridges remain other lanes).

`LeanProofs/BoundedCalculi.lean` (the aggregate import) is a **compile marker
only** — it proves the nine calculi + support module can coexist in one build,
not that they compose, and it is not imported by `LeanProofs.lean`.

Verification basis: every module compiles clean (`lake env lean`, exit-code
receipts under `.governor/verify_receipts/`), zero `sorry`/`admit`/
`native_decide`, axiom footprints re-attested 2026-07-01 via `#print axioms`
(all ≤ `[propext, Quot.sound]`). Adversarial audits (codex) per slice; trail in
`.governor/loop.json` and `docs/CHANGELOG-scratch-campaign.md`.

## Proof-shape classes (roadmap §3)

`pos` positive composition/cut · `wit` witness dependency · `excl` constructor
exclusion · `comp` non-collapse under composition · `def` definitional/trivial
· `spec` specimen-backed · `surr` surrogate-only.

## The family — ANNEX (six bounded calculi)

| Module | Local judgment | Positive rule | Non-collapse / failed cut | Strongest | Weakest | Shapes | Axioms |
|---|---|---|---|---|---|---|---|
| `TemporalCustody` | `TemporallyValid` | `checked_action_temporally_valid`, `fully_checked_…` | `citation_time_validity_does_not_imply_execution_admissibility`; per-gate blockers; `fresh_signed_artifact_does_not_imply_live_epoch` | `temporally_valid_iff_all_use_time_gates` + the citation/execution wall (minimal-pair witnessed) | per-gate projection lemmas (inversion-cheap) | pos, wit, spec | none |
| `SurfaceProjection` | `ProjectionAuthorized` | `retained_witnesses_authorize` | `demanded_atom_without_retention_or_conversion_blocks_authorization`; `log_emission_does_not_prove_truth`/`_authorization`; lift non-discharge pair | `authorized_projection_supplies_every_demanded_atom_by_retention_or_conversion` | `demandsB` unfolding lemmas | pos, wit, excl | propext |
| `RefusalDenial` | `DenialValid` (+ `LegibleFor`) | `signed_denial_valid` | silence / displayed-refusal ⇒ valid-denial walls | signed-denial characterization | display-side def lemmas | pos, wit, excl | none |
| `BoundaryArtifact` | `MayMint` | `authorized_exposure_may_mint` | internal-evidence ⇒ external-artifact wall | the mint gate inversion | — | pos, wit, **surr** (local `Exposure` stand-in; does NOT testify about `Admissibility.CrossBoundaryExposure`) | none |
| `ObligationResidue` | `ObligationDerives` (wrapper over `Witnessed.ResourceSequent.Derives`) | `claim_resource_path_preserves_obligation`, `bridge_resource_path_…` | `derivation_cannot_suppress_obligation_without_receipt`; `receipt_cannot_account_unrelated_obligation` | non-suppression under derivation (engine-backed, comp) | `receipt_accounts_only_its_named_obligation` (def) | pos, wit, comp | none / propext |
| `SafetyPreservation` | `SafeAllowed` | `safeAllowed_preserves` | `authorized_damage_step_cannot_be_safeAllowed` | the auth-vs-safety split pair | — | pos, wit, **spec** (`ToyState` substrate) | none |

## The family — lifecycle members (promoted to ANNEX, 2026-07-01)

Promoted per the custody decision above. Paths are now
`LeanProofs/BoundedCalculi/{ExecutionCustody,BootKernel,CheckpointSettlement}.lean`
(+ `MeasureAccounting.lean`, support module: generic `wsum`/`Split`
conservation machinery — not a calculus, no judgment, no authority). Each
carries the release-surface non-authority header. Goblin wards, stated in the
headers and binding on release notes: Execution Custody is a
**stage-separation calculus, not an actuator model**; BootKernel's
**capability accumulation is staged/nested monotonicity, not root omnipotence
and not signed operator authority**; CheckpointSettlement's law is
**occurrence-linear multiplicity preservation** (membership-level compaction
was rejected via the duplicate-collapse countermodel).

| Module | Local judgment | Positive rule | Non-collapse / failed cut | Strongest | Weakest / open | Shapes | Axioms |
|---|---|---|---|---|---|---|---|
| `ExecutionCustody` (L4) | `MayAttempt`/`MayCommit`/`CommitAttempted`/`DidExecute`/`DidNotExecute`/`CommitUnknown`/`PreservedSafety`/`DischargedObligation` | 5 positive rules + full specimen chains | 6-way witnessed ladder (`execution_custody_noncollapse_bundle`); `commitUnknown_testifies_to_neither` (zero-axiom crash-ambiguity wall) | the ladder bundle + CommitUnknown wall | `preservedSafety_does_not_imply_dischargedObligation` (receipt is a bare Bool). **Documented limits:** actuator boundary abstracted (`commitSent`/`outcome` independent fields — a local-model limit, not a claim); single-stage ticket flip (trajectory linearity lives in Sequent 2, post-v3) | pos, wit, spec | none |
| `BootKernel` (F) | `BootStep`/`BootReaches` + per-capability grants | `full_boot_reachable` (zero-axiom, every rung witnessed) | witness invariants `settled_requires_settlement_witness` + coverage (comp); anti-skip `cold_start_single_exit` (zero-axiom); trajectory freeze; ladder-entry inversions | the coverage invariant under composition | `kernel_boot_does_not_imply_root_omnipotence` (schema, labeled thin); `capabilities_accumulate` states the monotone nesting honestly | pos, wit, comp, spec | ≤ propext |
| `CheckpointSettlement` (G) | `CheckpointSettles` (occurrence-linear, `Split`-based) | `good_checkpoint_settles` + `compaction_is_real` | `checkpoint_mints_nothing`; `settlement_preserves_live_multiplicity`; unknown-commit + observation-to-safety walls; `dropping_live_obligation_invalidates` (minimal pair) | live-multiplicity conservation (engine-backed) | dead-entry policy is a fixed parameter (**flagged open**: consumers treating discharged records as receipts must demand a stricter `MustSurvive`) | pos, wit, comp, spec | ≤ [propext, Quot.sound] |

## Fenced evidence — NOT part of the v3 claim (v3.x)

Bridge work (scratch, fenced, cited as evidence the walls are provable, never
as promoted authority): `TemporalToSurfaceBridge` (surrogate specimen, two
failed-cut axes with minimal pairs), `TemporalSurfaceAdapter` (freshness-only
map, three no-laundering guards), `TemporalToSurfaceBridgeWiring` (real-module
probe; non-transfer bundle is toy-target/specimen-labeled; bidirectional
mutual-nonimplication with product-orthogonality scope stated).

Sequent ladder (scratch, post-v3 by the release boundary): `BridgeSequent`
(S0+S1 — indexed bridge cut, **zero-axiom** syntactic no-free-cross-cut,
provenance-roots-in-assumptions), `ExecutionSequent` (S2 — conservation of
authority, no-double-spend, Δt wall), `ExecutionObligationSequent` (S3 — three
linear books, receipt-linearity wall, exact discharge inversion). S4 (bridge
composition / non-transitivity law) is **unbuilt by design** — no composition
rule exists anywhere, and that absence is load-bearing.

## Release-boundary statement

> v3 proves the family exists. Sequents prove how the family composes without
> becoming a god-calculus — and they are the next phase, named here, not
> claimed here.
