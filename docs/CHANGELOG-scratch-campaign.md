# Changelog — bounded-calculi / sequent-ladder scratch campaign

## 2026-07-01 — v3 release prep addenda
`lakefile.toml`, `WHAT-THIS-PROVES.md`, `README.md`, `CHANGELOG.md`

- **CI-coverage gap closed (operator-spotted):** nothing globbed
  `BoundedCalculi/` — the `LeanProofs` lib owns only its root module, which
  deliberately does not import the aggregate — so the v3 release surface was
  invisible to `lake build`/CI (explains the earlier full-build-green-while-
  scratch-broken anomaly). Added a `BoundedCalculi` lean_lib + default target;
  bumped package version to 3.0.0. Build coverage, not promotion: the
  `LeanProofs.lean` boundary is unchanged. `Scratch/` stays uncovered by
  design (compile-is-contact, checked per-file by the campaign loop).
- **Prior-art section** added to `WHAT-THIS-PROVES.md` (Relation to prior
  work): Gentzen/cut, Girard/linear logic, ABLP access-control calculus,
  Appel–Felten PCA, Necula PCC, Lamport/TLA, W3C PROV, Denning IFC,
  SPKI/SDSI + macaroons, in-toto/SLSA — with the anti-flattening claim (the
  distinct object is bounded lifecycle calculi with explicit non-collapse
  walls; the welding is the novelty, not the ancestors) and a pointer to the
  fuller two-sided map in the papers repo. README links it.
- **DOI wording corrected:** GitHub release creation mints the DOI, not the
  tag alone.

## 2026-07-01 — v3 promotion executed (Option A): Bounded Lifecycle Calculi
`LeanProofs/BoundedCalculi/{ExecutionCustody,BootKernel,CheckpointSettlement}.lean`
(moved from Scratch, ANNEX release-surface headers),
`LeanProofs/BoundedCalculi/MeasureAccounting.lean` (new support module),
`LeanProofs/BoundedCalculi.lean` (aggregate: +4 imports, hardened compile-
marker language), `LeanProofs/Scratch/{ExecutionSequent,ExecutionObligationSequent}.lean`
(re-pointed at MeasureAccounting/new namespaces), `README.md`,
`WHAT-THIS-PROVES.md`, `CHANGELOG.md` (v3.0.0 entry), `docs/V3-RELEASE-LEDGER.md`

- Operator decision: promote all three lifecycle members into the
  `BoundedCalculi/` ANNEX **release surface** (not promoted-kernel authority),
  with ugly non-authority headers + goblin wards (stage-separation ≠ actuator;
  accumulation ≠ escalation; membership-compaction rejected, Split law chosen).
- Naming stack ratified: umbrella **Custody-Aware Authority Semantics**;
  release **v3.0.0 — Bounded Lifecycle Calculi**; next campaign
  **Custody-Indexed Sequents** (v3.x); ambition **Custody-Indexed Gentzen
  System** (v4, roadmap prose only).
- Layering fix forced by promotion: generic measure machinery extracted to
  `MeasureAccounting` so the release surface imports no scratch (ANNEX →
  Witnessed/ANNEX only; Scratch → ANNEX).
- Gate battery green: full build; four audit scripts exit 0; per-file sweep
  PASS; footprints re-attested post-move; `LeanProofs.lean` untouched.

## 2026-07-01 — v3 release-readiness audit + release ledger
`docs/V3-RELEASE-LEDGER.md` (new), `docs/ROADMAP-bounded-calculi.md` (§10 all
slices L0–L6 closed)

- Ratified release boundary (operator, via ChatGPT relay): **v3 = the bounded
  mini-calculi family; v3.x = sequent scratch; v4 = indexed sequent system
  ("custody-indexed Gentzen"), if it earns the name.** Sequents S0–S3 are
  fenced evidence, not part of the v3 claim; S4 stays unbuilt by design.
- Cold codex release audit: **YELLOW, boundary properly scoped.** Blockers
  named: the L1 theorem-inventory table (→ closed by the ledger) and an
  explicit operator decision on Execution Custody / BootKernel /
  CheckpointSettlement release status (promote vs. ship as fenced scratch
  evidence — custody act, operator-only). Actuator-limit and compile-marker
  language now stated in the ledger.

## 2026-07-01 — G: CheckpointSettlement (family complete)
`LeanProofs/Scratch/CheckpointSettlement.lean` (new)

- Occurrence-linear settlement judgment over `ResourceSequent.Split` (first
  draft's membership-level rule let duplicates collapse — codex countermodel;
  Split closes it). `checkpoint_mints_nothing` (zero-axiom) blocks the whole
  upgrade family; `settlement_preserves_live_multiplicity` +
  per-entry count conservation; unknown-commit and observation-to-safety
  walls; minimal pair `dropping_live_obligation_invalidates`;
  `compaction_is_real`. Dead-entry policy flagged open (receipts-vs-droppable
  is consumer policy).

## 2026-07-01 — F: BootKernel audit closure
`LeanProofs/Scratch/BootKernel.lean` (modified)

- Codex audit YELLOW → closed: trajectory-level freeze
  (`reaches_from_settled_freezes_baseline`), ladder-entry inversions
  (`settled_entered_only_from_observed`, `execution_entered_only_from_minting`,
  zero-axiom), and the honesty fix — `capabilities_accumulate` states the
  monotone capability nesting as a theorem instead of denying it; the
  omnipotence theorem docstring demoted to schema (the hard walls are the
  anti-skip theorem, the witness invariants, and the absent root/signature
  vocabulary).
- Also landed pre-audit: coverage invariant
  (`settled_witness_covers_observed_baseline`).

Campaign-scoped change tracking (operator directive 2026-07-01: version/release
history stays in the root `CHANGELOG.md`; this file tracks the SCRATCH campaign
as it lands, commit grouping is not the unit of record). Everything below is
`Custody-Class: SCRATCH` unless stated; nothing here changes a promoted kernel,
an import boundary, or the public surface. Verification receipts land under
`.governor/verify_receipts/` (gitignored; durability = receipt content hashes,
not git). Program counter: `.governor/loop.json`.

Invariant under audit throughout: *no artifact may testify beyond the stage it
actually survived.*

## 2026-07-01 — F: BootKernel (initial)
`LeanProofs/Scratch/BootKernel.lean` (new)

- Boot ladder ColdStart→…→ExecutionEnabled with per-capability grants;
  witnessed settlement (`settled_requires_settlement_witness`, invariant under
  composition); anti-skip wall `cold_start_single_exit` (zero-axiom);
  `full_boot_reachable` specimen (zero-axiom); settlement freeze; no
  root/signature vocabulary (structural absence).

## 2026-07-01 — Sequent 3: obligation/receipt books through execution
`LeanProofs/Scratch/ExecutionObligationSequent.lean` (new),
`ExecutionSequent.lean` (wsum machinery generalized to any element type)

- Three linear books (tickets, obligations, receipts) threaded through
  execution trajectories. Commit books a debt; discharge consumes one
  obligation occurrence AND one receipt occurrence naming it (receipt
  linearity added after codex named the reuse hole: one stipulated receipt
  could license two discharges).
- `obligation_accounting` + `receipt_accounting` +
  `ticket_accounting_with_obligations` (triple-entry conservation);
  `one_receipt_cannot_license_two_discharges`; `no_silent_discharge`; exact
  `discharge_inversion` (zero-axiom); refusal walls `cannot_discharge_unowed`
  / `cannot_discharge_without_held_receipt`; lifecycle + minimal-pair
  specimens (zero-axiom).

## 2026-07-01 — Sequent 2: execution ticket linear sequent
`LeanProofs/Scratch/ExecutionSequent.lean` (new)

- Linear turnstile `Γ ; τ ⊢[Execution] committed(t, now) ⊣ τ_spent` over
  `Witnessed.ResourceSequent`'s `Split`/`Consumes` (reused, not re-derived).
- **Conservation of authority** (`trajectory_accounting`): initial measure =
  spent + residual, for every measure `w`; corollaries `commits_le_initial`,
  `ticket_commits_le_initial_occurrences` (general no-double-spend),
  `id_commits_le_initial_id_occurrences` (anti-forgery accounting). Built as
  the codex-audit-requested generalization of the singleton walls.
- Singleton walls: `one_ticket_cannot_commit_twice`,
  `spent_context_cannot_commit_anything` (consumption exhausts authority).
- Δt wall: `stale_at_commit_cannot_commit` +
  `fresh_at_attempt_does_not_survive_to_late_commit` (same ticket, same
  context, only the tick differs — freshness is evaluated at commit).
- Residue preservation via the reused engine
  (`unconsumed_ticket_survives_commit`).
- Non-transfer: `sequent_commit_does_not_imply_execution`; judgment vocabulary
  structurally cannot state `DidExecute`.
- Closes the E-audit ticket-linearity completeness item (single-stage flip →
  trajectory-level linearity).
- Gates: compile [pass]; axioms ≤ [propext, Quot.sound] (three theorems
  zero-axiom); codex audit YELLOW → requested accounting theorem built → green.

## 2026-07-01 — Sequent 0+1: indexed bridge cut + no-free-cross-cut
`LeanProofs/Scratch/BridgeSequent.lean` (new)

- Sequent layer organizing EXISTING judgments (`TemporallyValid`,
  `ProjectionAuthorized`, surface-side bridge evidence); two rules (`ax`,
  `bridgeCut`); no master judgment; no rule mints `tValid` or `bEvid`.
- Sequent 0: `bridge_cut_derives` + `concrete_sequent_sound` — the licensed
  crossing, sound against real `ProjectionAuthorized` over real objects.
  Soundness genuinely consumes the temporal premise (closes the C-audit
  dead-weight finding at this layer).
- Sequent 1: `no_free_cross_cut` — ZERO-AXIOM syntactic non-derivability for
  all temporal-only contexts, all surface targets, all derivation depths
  (relative to the declared rule set, stated explicitly per audit).
- Provenance: `pAuth_derivation_roots_in_assumptions` (audit-requested) —
  every surface authorization traces to actual context membership.
- Gates: compile [pass]; syntactic layer zero-axiom, soundness [propext];
  codex audit YELLOW → docstring scope qualification + provenance theorem →
  green.

## 2026-07-01 — Run E: ExecutionCustody audit + CommitUnknown fix
`LeanProofs/Scratch/ExecutionCustody.lean` (modified)

- Audit: 6-step non-collapse ladder genuinely witnessed (specimen-backed
  existentials, paired positives). Primary gap: `CommitUnknown` was decorative.
- Added `commitUnknown_testifies_to_neither` (zero-axiom): an unknown substrate
  outcome testifies to NEITHER execution nor non-execution (crash-ambiguity
  laundering blocker).
- Completeness items recorded (ticket linearity → closed by Sequent 2;
  actuator causal boundary; `DischargedObligation` decoupling).

## 2026-07-01 — Run C: L3 no-free-cut strengthening
`LeanProofs/Scratch/TemporalToSurfaceBridgeWiring.lean` (modified)

- Codex audit found the positive path carried temporal validity as dead weight
  (real `ProjectionAuthorized` is temporal-blind). Operator chose in-vocabulary
  strengthening.
- Added `surface_authorized_does_not_imply_temporally_valid` (reverse cut) and
  `temporal_surface_mutual_nonimplication` (bidirectional independence
  capstone; product-orthogonality scope stated precisely per second audit
  round). Both [propext].

## 2026-07-01 — Governor plane + roadmap reconciliation
`.governor/` (new), `docs/ROADMAP-bounded-calculi.md` (§10 statuses + §11
as-built ledger), `docs/worked-examples/temporal-surface-vocabulary-alignment.md`
(relocated from the duplicate `LeanProofs/docs/` roadmap, retitled as an
alignment log)

- Two-roadmap fork reconciled; duplicate deleted; codex's over-run (adapter,
  wiring probe, ExecutionCustody) recorded as contact, then ratified into the
  queue.
- Per-repo `.governor/loop.json` program counter stood up (nq precedent:
  program counter + custody trail in git, runtime receipts gitignored).
- Verification pattern established: `governor verify-run` exit-code receipts +
  `#print axioms` footprint checks + codex adversarial audits (codex =
  auditor; bwrap sandbox blocks codex-as-builder in this environment).

## Queue (next)

- **SEQ3** — obligation/residue threaded through execution
  (`ObligationResidue` already imports `ResourceSequent`; natural join).
- **F** — BootKernel / BaselineSettlement stages + non-collapse laws
  (roadmap §7).
- **G** — CheckpointSettlement preservation theorems (roadmap §8).
- **SEQ4** — bridge composition laws (only after SEQ2/SEQ3; no composition
  rule exists anywhere yet, by design).
- Actuator causal boundary (E-audit note) — candidate slice.
