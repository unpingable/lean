# Changelog — bounded-calculi / sequent-ladder scratch campaign

## 2026-07-01 — post-v4 C2: decidable screens (screening as computation)
`LeanProofs/Scratch/DecidableScreens.lean` (new), `lakefile.toml` (CI root).

- `DecSystem`: finite systems as boolean rule tables + complete enumerations.
  Every v4 screen gets an executable Bool version with a PROVED soundness iff
  against the Prop screen: `fundableB`/`universalStampB`/
  `evidenceCurrencyFreeB`/`crossBridgeB`/`substantiveB`/
  `universalCrossroadsB`/`masterFreeB`.
- **Screen verdicts by kernel computation**: the zoo's hub fails `MasterFree`
  by `decide`; the sink PASSES — `sink_master_free_by_decision` is a
  `MasterFree` proof obtained by computation + iff, not hand case analysis;
  the stamp system fails the currency screen likewise. The proof-native seed
  of the v6 checker.
- Discipline note: `Classical.choice` crept in via `by_cases` on undecidable
  Props and was purged (Bool-cases on the executable screens instead) —
  everything within `[propext, Quot.sound]`. Kernel `decide` only; the native
  decision procedure stays forbidden. Walls (derivability itself) are NOT
  decided here — v6 work, stated.

## 2026-07-01 — post-v4 C1: the zoo opens
`LeanProofs/Scratch/Zoo.lean` (new), `lakefile.toml` (post-v4 files + zoo
added to the CI lib roots — the coverage rule, applied on schedule this time).

- Two NEW catch mechanisms caged, joining the proven two (screen refutation;
  inexpressibility):
  - **summary-as-authority → discipline unsatisfiability** (zero-axiom,
    two-line catch): a system where an emitted summary also funds
    authorization cannot even STATE `EvidenceNeverConcluded` — it forfeits
    every v4 wall visibly. Clean neighbor: logs exist, logs fund nothing
    (`clean_summary_discipline`). *Log emission does not prove authorization.*
  - **universal crossroads → MasterFree refutation**: `hubSystem` (A⇄H⇄B full
    mediation) caught; TRUE minimal-pair contrast `sinkSystem` (drop only the
    outbound rules — receiving from everyone is not mastery; mediating every
    pair is) passes the screen.
- Registry section records the resident cages (stamp, fluency, refresh,
  cleanse, projection-as-mint, checkpoint-as-discharge, ticket/commit ANNEX
  walls) — cited, not duplicated. TODO: skeleton replays of the four ANNEX
  entries; `CaveatBlind` screen design before its cage.

## 2026-07-01 — post-v4 F3–F5: caveat inheritance + the two docs artifacts
`LeanProofs/Scratch/CaveatSequent.lean` (new; **entirely zero-axiom**; codex
first-pass GREEN — first of the campaign), `docs/AG-AUDIT-CHECKLIST.md` (F4),
`docs/ZOO-TEMPLATE.md` (F5).

- **F3 — the duality**: with demand semantics "a use must accept every caveat
  its funding evidence carries," funding-antitone (`step_shape`) IS
  burden-monotone. One law, two faces: Δt (funding narrows as budget decays)
  and caveats (burdens grow as evidence derives).
  `admissible_steps_grow_caveats` (one-shot, the F1/F2 pattern);
  `caveat_dropping_is_inexpressible` (cleansing requires new evidence, never
  derivation); `derived_evidence_inherits_caveats` (chains);
  `burdened_evidence_cannot_fund_unaccepting_use` +
  `all_burdened_context_cannot_fund_unaccepting_use` (audit-requested
  context-general wall); positive + minimal pairs. **Closes the parked 4th
  refusal slice** (burden preservation under derivation; boundary transfer
  explicitly out of scope). Named unscreened attack: caveat-blind demand
  (`CaveatBlind` screen = follow-up).
- **F4 — AG audit checklist**: the v4/post-v4 screens and walls translated
  into applicable questions over live constellation schemas (receipt kinds ×
  gates; crossroads; midpoint matching; provenance rooting; refresh lanes;
  burden survival; linearity; compaction custody) — each item citing its
  backing theorem and its screening caveats. For the AG session to apply;
  findings live in AG's loop, not here.
- **F5 — zoo cage template**: the six-part cage schema (FORBIDDEN specimen /
  attack shape / catch theorem / TRUE-minimal-pair contrast / caveats /
  expected refusal) + the C1 inventory (11 cages; 4 effectively done, 7 TODO,
  1 needs a new screen designed first). Pattern proven by `stampSystem` and
  `fluentSystem`.

## 2026-07-01 — post-v4 F2: fluency as evidence-currency attack
`LeanProofs/Scratch/FluencySequent.lean` (new). **Entire file zero-axiom.**

- **The thesis**: confidence/fluency is claim-BLIND; reliance bridges demand
  claim-INDEXED provenance. The blindness is the load-bearing modeling choice
  (a witnessed confidence-about-c would be a different, indexed evidence
  species — stated, not smuggled).
- **The root theorem** (`reliance_roots_in_provenance`): under ANY evidence
  calculus over the clean system, a derivation of `mayRely c` either assumed
  reliance outright or holds `provenance c` literally in context. Confidence,
  recall, and claims cannot be the root. HighConfidence ⊬ MayRely as a
  two-case normal form, at any depth.
- **The upgrade killer** (`confidence_cannot_be_upgraded_to_provenance`, via
  the one-shot `steps_into_provenance_come_from_provenance` + chain version):
  no evidence calculus can derive provenance from confidence — provenance
  requires its own read, at every confidence level. Fluency ⊬ Provenance,
  constructively.
- Corollaries with explicit contexts (`high_confidence_does_not_mint_may_rely`,
  `recall_does_not_authorize_reliance`) + the positive pair
  (`provenance_funds_reliance`).
- **The attack specimen** (`fluentSystem`, fenced FORBIDDEN): the clean system
  plus claim-blind sway rules — nothing dropped (codex caught the first
  draft narrowing the obligation space; fixed to a true one-family minimal
  pair). Confidence becomes a `UniversalStamp`; the currency screen catches
  the system. *A system that lets fluency fund reliance has installed a
  universal currency, and the screen names it.*
- Doctrine source cited (readout arc: HighConfidence⊬MayRely, Fluency⊬
  Provenance, Recall⊬Reliance): this is its sequent-theoretic face —
  *confidence does not lie; confidence exceeds jurisdiction* — here,
  jurisdiction = funding scope, and confidence has none.
- Codex YELLOW → minimal-pair fix applied. Named for F3: entailment-root
  theorem for provenance from arbitrary contexts, then caveat inheritance
  from the provenance root into `mayRely`.

## 2026-07-01 — post-v4 F1: Δt as derivation step (+ campaign map captured)
`LeanProofs/Scratch/DeltaTSequent.lean` (new), `docs/POST-V4-CAMPAIGN.md`
(new — ratified F1–F7/C1–C3 ordering, deferred list, the binding guard).
Post-v4 work; v4.0.0 was tagged and released clean (CI green, DOI minted)
before any of this landed.

- **The thesis**: time passing is an evidence-derivation step; the v4
  anti-currency law (`step_shape`) IS freshness decay. Evidence carries a
  remaining-validity budget; a tick spends one unit; demanding uses require
  minimum remaining budget.
- **The killer theorem** (`refresh_is_inexpressible`, zero-axiom): no
  evidence calculus over the Δt system can contain a refresh step — the
  discipline's law makes it UNSTATABLE, not merely refused. Renewal requires
  new evidence (a new read), never derivation from the old. Generalized per
  audit to the full characterization `admissible_steps_decay` /
  `admissible_chains_decay` (zero-axiom): ANY admissible step into evidence
  comes from evidence with at least as much budget, for every calculus over
  the system.
- **The wall** (`stale_context_cannot_derive_demanding_use`, zero-axiom):
  stale-holding contexts cannot derive demanding uses at any depth — proved
  through the read-rooted machinery (roots-in-read + chain decay +
  membership). Cartesian policy; linear version named follow-up.
- **The exploit pair** (`delta_t_exploit_blocked`): same origin — the aging
  chain `ev R →* ev (R−n)` exhibited, not asserted — funds at hold time,
  refused after elapsed time. Valid-then ⊬ valid-now, formally.
- Codex YELLOW → tightened: system-relative scope of the killer theorem
  stated; model-encodes-decay honesty (hosting claim, not ontology of time —
  per the campaign guard); Cartesian restriction flagged; correspondence to
  TemporalCustody/ExecutionSequent kept as cited analogy, not wired
  equivalence.
- Next per the ratified order: **F2 — fluency as evidence-currency attack.**

## 2026-07-01 — v4.0.0 release prep (doc sweep)
`CHANGELOG.md` (4.0.0 entry), `README.md` (v4 current release),
`WHAT-THIS-PROVES.md` (v4 section), `docs/V4-RELEASE-LEDGER.md` (new),
`CITATION.cff` (title/version/abstract — the 1.0-era "not a sequent calculus"
non-claim explicitly re-scoped to the stable kernel surface, where it remains
true), `lakefile.toml` (version 4.0.0; new `CustodyIndexedSequents` lean_lib +
default target so the release object is CI-covered — the v3 lesson applied;
build coverage ≠ promotion, modules remain SCRATCH),
`docs/ROADMAP-bounded-calculi.md` (both releases recorded; v5 campaign named).

- Release claim wording locked per audits: "structural READ discipline"
  (not "all structural rules"); cut elimination explicitly deferred to
  **v5 — Custody-Preserving Normalization**.

## 2026-07-01 — final v4 blocker: derived evidence + evidence-currency screen
`LeanProofs/Scratch/EvidenceCalculusSequent.lean` (new; additive). Codex
verdict: **GREEN — v4 EARNED.**

- **The coupled design**: `EvidenceCalculus` = a step relation with two laws —
  `step_shape` (funding never widens along derivation: *the rule relation is
  the sole authority map; derivation navigates it, never extends it*) and
  `step_targets_evidence` (steps produce evidence only — fences the
  derive-to-target bypass, a real hole found and closed at design time).
  `EEntail` adds a `derive` rule to the policy-parameterized sequent;
  derivation inputs are paid through the context policy.
- **Enforcement (zero-axiom core)**: `echain_funding` (funding monotone
  backward along chains); `stamps_are_inherited_not_minted` (universality
  cannot be manufactured, only inherited — one line, the depth lives in the
  laws); `derivation_funds_only_what_origin_funded` (every crossing consuming
  derived evidence traces to a read origin whose original scope included that
  crossing — existential inclusion, honestly scoped per audit);
  **`eentail_iff_read_rooted`** (audit-requested capstone: derivability ≡
  read-rooted normal form — every cut at any depth structurally carries its
  read origin, chain, and funding; no derivation shape lacks its custody
  chain).
- **Screening**: `UniversalStamp` (shape inspection — the rule relation at the
  evidence position, not index topology); `EvidenceCurrencyFree` (universality
  exists only degenerately). Detection pair: fenced FORBIDDEN `stampSystem`
  caught (`stamp_system_not_currency_free`), diamond clean
  (`diamond_no_universal_stamp`). Named false negative: multi-currency
  evidence below the universal threshold (consumer policy question).
- Contract notes advertised: closed-index wall over `EEntail` requires the
  evidence calculus to respect the index set (`hstepclosed`); over-wide rule
  relations are honest authorization, not laundering.
- **ALL v4 BLOCKERS CLOSED.** v4 tag decision → operator.

## 2026-07-01 — v4 blocker 3: structural-policy parameterization
`LeanProofs/Scratch/StructuralPolicySequent.lean` (new; additive — the audited
skeleton is untouched and recovered as an instance)

- **Context discipline is now a system parameter.** `ContextPolicy` abstracts
  the one operation both disciplines share — `Reads c j c'` ("obtain a
  judgment, leaving a residual") — with two laws; `PEntail` threads residuals
  through both premises of every cut (`Γ ⊢ j ⊣ Γ'`). Cartesian instance:
  reading is free. Linear instance: reading is `ResourceSequent.Consumes`.
- **The pricing pair** (the slice's reason to exist): one system, one rule
  citing the same judgment twice — `cartesian_contraction_free` derives from
  a single occurrence; `linear_contraction_priced` proves the SAME derivation
  impossible under the linear policy; `linear_pay_twice` shows two occurrences
  fund it. Contraction is a policy with theorems, not an assumption. Plus
  `linear_depletion` (monotone) and `linear_every_derivation_pays` (strict,
  audit-requested: nothing derives for free).
- **The v4 discipline stack re-proved parametrically** over any conforming
  policy: evidence-only-by-reads, the normal form (`pentail_iff_rooted`),
  provenance chains (`pentail_provenance` — each hop's evidence obtained by a
  licensed read at its thread state), closed-index wall. Zero-axiom core.
- **Cartesian collapse** (`pentail_cartesian_iff`, zero-axiom, bidirectional
  induction): the parameterized skeleton collapses to the audited `Entail` —
  S4 and the diamond recover compositionally.
- Codex YELLOW → tightened: honestly named READ-DISCIPLINE parameterization
  (no primitive split/merge/exchange algebra — named extension, not claimed);
  strict payment theorem added. Confirmed remaining blockers: derived-evidence
  extension; EvidenceCurrencyFree. Named follow-up: full SEQ2/SEQ3 equivalence
  (not claimed here).

## 2026-07-01 — v4 blockers 1+2: MasterFree + second instance (+ mismatch wall)
`LeanProofs/Scratch/CustodyIndexedSequent.lean` (extended; operator ruling: no
interim DOI, plow through)

- **MasterFree** (blocker 1): a master is formalized as a **universal
  crossroads** — a substantive index every other substantive index bridges
  into and that bridges out to every other; `crossroads_mediates_every_pair`
  states the god-calculus signature; `s4_master_free` proves the S4 system
  clean by finite case analysis (codex: non-vacuous). Honest caveats in-file
  per audit: this is universal-hub *screening*, not anti-authority
  enforcement — false negative = evidence-currency master (an evidence-only
  token funding every bridge; `EvidenceCurrencyFree` screening named as
  follow-up), false positive = benign router (index-level screening
  over-approximates).
- **DiamondInstance** (blocker 2): genuinely independent second instance —
  branching topology A→B→D vs A→C→D; provenance chains *name the route
  taken*; `diamond_unfunded_route_closed` (reaching the target one way does
  not open the other way; uses the discipline).
- **MidpointMismatch wall** (surfaced by the MasterFree design):
  `index_connectivity_does_not_imply_derivability` — A→B and B→C hold at the
  index level, everything funded, composite still underivable because the
  midpoint judgments differ (`b1` produced, `b2` consumed). Bridges connect
  judgments, not indices; index analysis is a smell detector, not a
  conversion license. Zero-axiom.
- Remaining v4 blockers: structural-policy parameterization (linear contexts
  as a system parameter — merge the Split lane); derived-evidence extension
  (evidence minted through its own paid calculus — the validator shape);
  EvidenceCurrencyFree screening.

## 2026-07-01 — v4 CANDIDATE: generic custody-indexed sequent skeleton
`LeanProofs/Scratch/CustodyIndexedSequent.lean` (new; post-v3.0.0; does NOT tag
v4 — release classification is the operator's)

- **The generalization slice**: `System (J, Ix, ix, Rule)` + generic `Entail`.
  ONE discipline condition — `EvidenceNeverConcluded` (no rule concludes an
  evidence judgment) — yields by induction, for every conforming system:
  evidence enters only by assumption (generic no-default-transitivity: nothing
  can synthesize evidence, composite or otherwise); **`entail_iff_rooted`, the
  normal-form theorem** — derivability is EQUIVALENT to evidence-rooted
  chaining, i.e. no derivation shape exists in which a cut's evidence is not
  in custody, at any depth (the "cut cannot erase bridge evidence" target in
  characterization form); provenance chains as first-class enumerable lists;
  the generic index-closure wall (needs no discipline at all); weakening
  declared as the Cartesian polarity (linear contexts = resource lane, named).
- **S4 recovered as an instance**: `s4_entail_iff` bidirectional,
  rule-for-rule; the generic machinery replays the specimen's provenance and
  no-synthesis theorems. **ENTIRE FILE ZERO-AXIOM** (not even propext).
- Codex verdict: **YELLOW, v3.1-first** — genuinely generic (binary Cartesian
  rule class), normal form real (no erasure countermodel constructible), no
  composite leak, recovery real. Fixed per audit: anti-master header overclaim
  retracted (the skeleton provides no master but does not prevent one;
  `MasterFree` predicate is v4 design work); multi-role exclusion stated
  (derived certificates / evidence-producing subcalculi — the validator shape
  — are the other v4 frontier).
- **v4 blockers (named)**: MasterFree wellformedness predicate + theorem; a
  second independent instance; structural-policy parameterization (merge the
  Split-based linear lane); derived-evidence extension.

## 2026-07-01 — Sequent 4: bridge composition + non-transitivity (ladder complete)
`LeanProofs/Scratch/BridgeCompositionSequent.lean` (new; post-v3.0.0, opens the
Custody-Indexed Sequents campaign)

- Composition finally exists — as **two explicit cuts** through the shared
  intermediate judgment (Temporal→Surface→Boundary, boundary hop specimen-typed
  on the real `BoundaryArtifact.MayMint`, exposure class). Five calculus
  indices; deliberately no `bridgeTB` index for a composite to live in; no
  rule concludes evidence of any kind.
- **Zero-axiom syntactic layer:** `composition_cannot_erase_bridge_evidence`
  (every mint traces to its full custody chain; bounded-normal-form scope
  stated per audit), `mint_without_downstream_axioms_requires_all_three`
  (audit-requested forcing version: strip the assumed-outright escape hatches
  and all three evidences are mandatory), `no_free_transitivity`,
  `first_bridge_alone_does_not_compose` (deriving hop one accumulates zero
  boundary authority), and the S1 temporal wall re-established under the
  extended rule set (each new cut pays its preservation case).
- Soundness `[propext]`: TS cut consumes the temporal premise (S0 discipline);
  SB cut discharges from boundary evidence alone — declared as the
  non-transitivity content; codex ruled the pairing premise **syntactically
  load-bearing** (deleting it collapses the provenance chain).
- Honesty pair: sealed-boundary evidence is syntactically assumable,
  semantically unsatisfiable (`sealed_boundary_evidence_unsatisfiable`);
  soundness never converts.
- Sequent ladder S0–S4 COMPLETE. Next horizon: v4 custody-indexed Gentzen —
  generalize the bounded-normal-form provenance to induction over a rule set
  with real left/right structural rules.

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
