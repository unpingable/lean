# Lean Proofs

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.20369489.svg)](https://doi.org/10.5281/zenodo.20369489)

Small, auditable Lean 4 formalizations for reasoning about evidence, standing, freshness, authority, witnessed transition, and the boundaries between them.

Development-order and custody discipline for contributors and coding agents
lives in [`AGENTS.md`](AGENTS.md) (in short: formalization leads code, and
compiling a theorem is neither a custody promotion nor a runtime-conformance
claim).

## Current release: 10.0.0 — View Semantics and Bounded Projection

*Distinguishability as a first-class axis: view refinement changes what is
distinguishable without minting transition authority.*

**v10.0.0 lands the view-semantics campaign**: a canonical distinguishability
core over finite view systems, an exact characterization of deterministic
bounded projection, a sound-and-complete finite checker with typed
certificates, and a custody adapter proving greater visibility constructs no
authority.

What v10 lands:

- **`ViewSemantics` core (UNRATIFIED-CANDIDATE, Mathlib-free)** — `View`,
  `Indistinguishable`, fine-to-coarse `Refines`, `Determines`, the weak/strong
  determination boundary with inhabited witnesses, composition laws with a
  finite-family join API, and rooted counterexamples: weak nondetermination is
  **not** closed under composition, while declared disclosure bounds compose.
- **Bounded projection** — `OperationallySufficient` stays existential (the
  general-safe fence); deterministic bounded sufficiency is characterized
  exactly by a refinement sandwich
  (`deterministicallyBoundedSufficient_iff_refinement_sandwich`); existence
  boundaries choose the required-action projection, never the budget; all
  four disclosure × sufficiency audit cells are inhabited.
- **Sixth-atom adjudication (negative, scoped)** — the axis adapter imports
  the resident bridge atom/family ontology; `no_resident_bridge_pair_pays_all_five`
  shows the literal all-five bridge premise is uninhabited there; disclosure
  is recorded as an **orthogonal view-context axis, deliberately not a sixth
  family atom**.
- **Finite checker** — `ViewAudit` returns two independent typed results
  (`PolicyCertificate`/`ActionConflict`, `BoundCertificate`/`ForbiddenDistinction`),
  each carrying concrete witnesses; soundness and reflection proved in both
  directions; all four quadrants execute without `native_decide` or a
  collapsed validity bit.
- **Authorized-trace custody adapter** — consumes a v9 `AuthorizedTrace`;
  observation refinement/join preserve the exact evidence and step sequence;
  `full_visibility_does_not_override_revoked_basis` and
  `full_visibility_does_not_supply_missing_authority` reuse the v9 walls.
- **Applications** — `BindingSourceAblation` factors its determination
  predicate exactly through canonical `Determines` (non-XOR, governed-trace
  quotient view); `MosaicRelease` and `CompartmentConflict` retained as
  SCRATCH compatibility wrappers over the canonical core; the P25 observation
  adapter is confined to an explicit Mathlib island.
- **Build/audit surfaces** — `ViewSemantics` and `ViewSemanticsApplications`
  join the default Mathlib-free targets; `ViewSemanticsMathlibIslands` builds
  explicitly; CI builds all three and runs the fail-closed footprint gate
  (36 receipts axiom-free; application/island footprints pinned exactly) and
  the isolation gate (closures Mathlib-free and custody-separated).
- **Compatibility and release control** — v10 removes the deprecated
  `LeanProofs.Admissibility.CalculusOne` import shim after retaining it through
  v9; downstream code must use `AdmissibilityKernels`. The template workflow
  that could create a GitHub release on a `lean-toolchain` change is also
  removed, keeping release and DOI minting under explicit operator control.

v10 makes **no** information-flow, noninterference, probabilistic-leakage,
side-channel, runtime-compliance, or transition-authority claim. All
ViewSemantics material is UNRATIFIED-CANDIDATE: the release archives the
tree; it is not a custody promotion. SCRATCH incubations landed since v9
(reversal-authority, credit/standing, signal-authority, and sibling
campaigns) ship in the archive and testify for nothing.

Release inventory: [`docs/V10-READINESS-LEDGER.md`](docs/V10-READINESS-LEDGER.md).

## 9.0.0 — Dynamic Traces and Profile Semantics

*Dynamic execution over static witnesses, and checker-facing profile semantics.*

**v9.0.0 opens the dynamic-claims campaign**: state-threaded traces in which
every hop carries the exact static `AuthorizedStep` witness it consumes — no
global `Admissible` judgment, no free composition — plus a minimal
profile-checker semantics specimen for the RRP admissibility-gate prototype,
the stack's first named runtime correspondence target.

What v9 lands:

- **`Admissibility/DynamicTrace.lean` (ANNEX)** — `DynamicStep` wraps the
  static execution bridge (the target state is `executeAuthorizedStep`,
  never guessed); `AuthorizedTrace` threads steps through governance state;
  revoked basis and revoked standing block dynamic steps; mutation-side
  standing without claim-side authority blocks; actor-indexed trace variants
  with attribution theorems; non-amend traces preserve the policy store.
- **`Admissibility/FreshnessDynamicTrace.lean` (ANNEX)** — freshness-gated
  discharge: a stale, expired, not-yet-valid, incoherent, non-preceding, or
  divergence-excessive observation cannot discharge the current obligation
  (one theorem per failure mode, riding the public `Freshness` kernel).
- **1.0 surface, additive** —
  `Execution.revoked_standing_cannot_be_authorized_step` lifts revoked
  standing to the execution layer. No existing 1.0 signature changed.
- **Ten specimen laws (all UNRATIFIED-CANDIDATE, unwired, formalization
  leading implementation)** — candidate formal laws for runtime seams,
  written before the runtimes that will cite them:
  `RRPProfileSpecimen` (claims derive only through admitting rules; effects
  require claims; missing/cannot-testify/stale/revoked evidence refuses;
  `profile_id` cannot substitute for `profile_digest`),
  `StandingProfileSpecimen` (schedule / operator ack / model output are not
  standing; standing is scoped and non-transferable),
  `WLPAppendAckSpecimen` (append acks and publications are custody
  evidence, never claim authority),
  `BridgeCustomsSpecimen` (source permit alone is no target permit; the
  bridge claim carries the cap; promotion is digest-addressed),
  `ActorTraceSpecimen` (actor A's hop is not actor B's standing; a
  truncated trace is no evidence),
  `LocalBoundaryPressure` (dropping `MergeAdmissible.left_sound` accepts a
  merge that leaks — the load-bearing field named by construction),
  `ScopedCertification` (watchers confined by claim class × scope;
  delegation does not compose for free; self-claims mint nothing;
  challenge ≠ revocation; universal authority unrepresentable),
  `SpendabilitySpecimen` (eligibility is contractible and never payment;
  capacity is linear; replays refuse; counts conserve — conserved ≠ safe;
  a revoked fork blocks the future but unwinds no effect),
  `CustodyFreshnessSpecimen` (freshness reads the producer clock only;
  custody hops never refresh; "recently checked somewhere" is modeled as
  the tempting evaluator and refuted by countermodel),
  `TemporalBasis` (time is testimony: freshness is admitted elapsed time
  under a declared witness contract; a fresh packet does not refresh old
  testimony; silence never clears; late success is not timely success;
  no GlobalTrustedTime).
  None of these testify for any runtime's compliance by themselves. Citation
  or adoption identifies the intended contract; conformance still requires an
  explicit mapping plus runtime evidence or a refinement proof. Lean custody
  promotion remains a separate review.
- **`Admissibility/DeferredWitness.lean` (ANNEX)** — the classifier
  reflection lemma `firstViolation_none_iff_lawful` is now proved (was
  documented as left to the host environment).
- **Build/audit surfaces** — Mathlib import-surface split
  (`AdmissibilityCustodyAnnex` cheap Mathlib-free custody target vs
  `AdmissibilityMathlibIslands`; the root `LeanProofs` aggregate builds
  explicitly, not by default), guarded by
  `scripts/check-mathlib-free-targets.sh`; CI builds the full aggregate and
  Mathlib islands explicitly and runs the repo audit scripts, so CI green
  means release-claim green; RRP↔Lean crosswalk at
  [`docs/RRP-LEAN-CROSSWALK.md`](docs/RRP-LEAN-CROSSWALK.md).

v9 is **not** a unified dynamic calculus, not process semantics, and not
runtime authority — per-hop static witnesses are the design. ANNEX and
UNRATIFIED-CANDIDATE material stays outside the 1.0 compatibility claim.

Release inventory: [`docs/V9-RELEASE-LEDGER.md`](docs/V9-RELEASE-LEDGER.md).

## 8.0.0 — Sequent Admissibility Island

*A Mathlib-free proof-theory specimen/library release.*

**v8.0.0 lands a kernel-checked sequent calculus in which no structural rule
is primitive and all four — weakening, contraction, exchange, cut — are
admissible**, plus a multiplicity-faithful textbook presentation proved
derivability-equivalent to it. The modules live under
`LeanProofs/ProofTheory/` (custody class UNRATIFIED-CANDIDATE; own
Mathlib-free `ProofTheory` `lean_lib`, build-graph enforced), with the
register fence and theorem inventory at
[`LeanProofs/ProofTheory/README.md`](LeanProofs/ProofTheory/README.md).

What v8 proves:

- **MembershipG3** — single-succedent intuitionistic `{atom, ⊥, ∧, ∨, →}`,
  contexts read by membership/subset, NO primitive structural rules; one
  `monotone` theorem (Γ ⊆ Δ) subsumes weakening/contraction/exchange
  size-preserving; general identity derivable (`initGen`); `cut` a
  **computable cut-free transformer** (degree-primary, size-secondary);
  `consistency` and `disjunction_property` immediate (cut-free by
  construction);
- **TextbookG3ip** — multiset-faithful G3ip as lists-quotiented-by-permutation
  (erasing left rules, multiplicity real, contraction not absorbed); admissible
  size-preserving exchange; the size-nonincreasing inversion package funds
  **admissible contraction** (`contractT`);
- **equivalence** — `textbook_iff_membership` (the specimen→textbook direction
  pays the contraction bill), discharging the specimen's original "not proved
  equivalent to textbook G3ip" caveat; cut/weakening/identity for the textbook
  calculus transport as corollaries (`cutT`, `weakenT`, `initGenT`);
- **audit in the build** — `Audit.lean` prints `#print axioms` receipts every
  build: zero user axiom declarations, everything ≤ `{propext, Quot.sound}`,
  **zero `Classical.choice`** (fully constructive).

v8 is **not** a governance kernel or doctrine unifier ("admissible" here is
literal Gentzen admissibility, the referent the governance vocabulary borrows;
no `Tier`/`Verdict`/`cap` coupling, no typeclass, no unifier; build coverage
is not promotion), not Mathlib `Multiset`-typed (List+Perm is the multiset with
its quotient explicit), not height-preserving cut, not proof search, and not
runtime enforcement.

Release inventory with audited theorem receipts:
[`docs/V8-RELEASE-LEDGER.md`](docs/V8-RELEASE-LEDGER.md); constructivity
footguns caught in-release: [`LeanProofs/ProofTheory/SCARS.md`](LeanProofs/ProofTheory/SCARS.md).

## 7.0.0 — Artifact Authority Profiles

*A Lean proof release for custody-aware authority semantics.*

**v7.0.0 proves the profile discipline**: profiles are local, crossings are
paid, receipts are not fungible across obligations, and coverage cannot be
minted. The campaign modules live under `LeanProofs/Scratch/` (custody
class SCRATCH, fenced, CI-covered — build coverage, not promoted kernel
authority); gap spec with the binding constitution (no shared custody
language, no master profile, local profiles + paid pairwise bridges) at
[`docs/V7-GAP-SPEC.md`](docs/V7-GAP-SPEC.md).

What v7 proves:

- **profiles do not compose for free** — holding two profiles' local
  material is not holding their cross-profile authority; conversion
  requires a declared paid bridge receipt, and with it the crossing
  composes — the only difference is the receipt
  (`profile_does_not_compose_for_free`,
  `cross_profile_conversion_requires_bridge`);
- **stage ascent pays each rung** — stage-n standing does not authorize
  stage n+1 (`profile_stage_noncollapse`); any ascent from j to k holds
  every intermediate rung receipt in custody, at any derivation depth
  (`ascent_pays_every_rung`). *No skipped rung, no bulk discount.*
- **receipts are jurisdiction-scoped, not fungible** — the generic
  evidence-jurisdiction screen (per-vocabulary, opt-in scopes), with the
  keeper wall `unmatched_context_cannot_convert`; the prior local walls
  recovered as exact instance iffs; receipt cross-use (bridge-as-rung,
  rung-as-bridge) caught; the once-escaped relation-promotion attack
  caught (`relation_promotion_fails_jurisdiction_screen`);
- **coverage cannot be minted** — derived evidence funds no obligation its
  origin could not fund (`derived_evidence_covers_no_more`); in
  single-scoped frames, covering k distinct obligations costs k distinct
  held receipts, exactly (`coverage_costs_receipts` + the 3-for-3 price
  witness). Broad custody is wealth, not forgery — when paid;
- **the screens stay honest about themselves** — a fully paid two-way
  bridge pair fails the index-level master screen
  (`two_way_profiles_fail_master_screen`): failing it is a smell, not a
  conviction; screening is not enforcement.

v7 does not claim a shared custody language ("Constellation Custody
Protocol" is a retired name), a master profile or universal artifact
authority schema, WLP semantics (envelope-only, untouched), runtime/JSON
schemas/AG integration, a profile registry, issuer-level
provenance-correlated portfolio accounting (the named v7.x remainder), or
a graded "too much coverage" policy screen.

Release inventory with audited theorem receipts:
[`docs/V7-RELEASE-LEDGER.md`](docs/V7-RELEASE-LEDGER.md).

## 6.0.0 — Finite Custody Checking

*A Lean proof release for custody-aware authority semantics.*

**v6.0.0 makes the v5 payment discipline finitely checkable.** A Lean-native
checker takes a liberal derivation tree and a finite context and returns a
typed verdict — `ok` with a positional occurrence trace, or a typed refusal
naming an offender. The campaign modules live under `LeanProofs/Scratch/`
(custody class SCRATCH, fenced, CI-covered — build coverage, not promoted
kernel authority).

What v6 proves:

- **the twins agree** — traced and untraced normalization return the same
  verdicts, the SAME offender on refusal, and residuals equal up to label
  projection (`tracing_preserves_verdicts`, `linearizeT_ok_projects`,
  `linearizeT_forgery_projects`); coherence holds over any tagged context.
  *Tracing is testimony about payment, never a change to who gets paid.*
- **every untraced run traces for free** — the canonical tagging bridge
  (`untraced_runs_trace_canonically`): tag a plain context with consecutive
  positions (provably unambiguous) and the traced twin runs with the same
  verdict and a position-distinct trace;
- **the checker is a decision procedure** — `Core.checkCtx` returns typed
  `CheckResult` (never bare Bool); soundness (`checkCtx_ok_sound`: ok ⇒ a
  valid linear derivation over the given context, trace labels = the read
  spine, no position pays twice, every trace entry from the given context)
  AND completeness (`check_complete`: sufficient counts ⇒ accept);
- **refusals are never mislabels** — the named offender's total demand
  genuinely exceeds supply (`check_refusal_excess`) and the offender is
  genuinely demanded (`check_refusal_offender_demanded`);
- **the verdict is finitely many comparisons** — the finite-support decision
  theorem (`firstDeficient_decides_check` + `support_covers_iff_all_covers`)
  reduces v5's infinite-label quantifier to counts over the read spine — the
  executable finite-support boundary v5 explicitly left unclaimed;
- **screens are computations** — the resident C2 layer (`DecidableScreens`,
  claimed into this surface): executable Bool forms of every v4 screen with
  soundness iffs; the zoo's hub/sink/stamp verdicts obtained by kernel
  `decide`. *Screening as computation, soundness as theorem.*

v6 does not claim a CLI, a runtime checker, Bridge Foundry, an artifact
profiler, a derivability decision procedure (it checks a given tree; no
proof search), a checker for arbitrary future structural systems, or a
master admissibility layer; offender identity across the two refusal
reporters is deliberately not claimed.

Release inventory with audited theorem receipts:
[`docs/V6-RELEASE-LEDGER.md`](docs/V6-RELEASE-LEDGER.md).

## 5.0.0 — Custody-Preserving Normalization

*A Lean proof release for custody-aware authority semantics.*

**v5.0.0 delivers the normalization layer for the v4 sequent skeleton.** The
thesis is the custody inversion: *classical normalization removes detours and
preserves derivability; custody-preserving normalization removes only
policy-licensed detours and REFUSES when removal would erase payment.* The
campaign modules live under `LeanProofs/Scratch/` (custody class SCRATCH,
fenced, CI-covered under `CustodyIndexedSequents` — build coverage, not
promoted kernel authority).

What v5 proves:

- **the already-normal theorem** — under the v4 discipline there are NO cut
  redexes; every derivation is read-rooted normal (`all_derivs_read_rooted`),
  so the detours worth pricing are *structural*, entering as explicit
  weakening/contraction/exchange nodes whose elimination preserves the
  custody chain (`chainOf_normalize`);
- **normalization is partial and policy-aware** — `linearize` pays every read
  with a distinct first-match occurrence and returns either a linear
  derivation or a **typed forgery refusal**; on success, occurrences are
  conserved for every measure (`linearize_ok_conserves`) and the evidence
  spine survives (`chainOf_linearize`);
- **counting decides normalization** — the decision theorem
  (`linearize_ok_iff_counts_suffice`): success ⟺ every label's demanded
  reads are covered by its occurrences; the refusal side is accounting-tied,
  not constructor-shaped (`excess_demand_forges`), and the named offender is
  itself a genuine excess-demand witness (`forgery_offender_is_excess`);
- **the positional occurrence trace proves who paid** — `linearizeT` records
  which original-context occurrence funded each read: no occurrence pays
  twice (`linearize_trace_occurrences_distinct`), nothing pays that was not
  there (`trace_mem_initial`), and the trace refines the read spine in order
  (`trace_labels_are_reads`). *Labels explain what was read; occurrence
  traces prove who paid.*
- **the same syntax, two verdicts** — the free-contraction tree embeds
  soundly under the Cartesian policy and is refused by linearization
  (`cartesian_statable_but_linearly_refused`). **Normalization cannot forge
  payment.**

v5 does not claim full Gentzen cut elimination, a full structural-rule
algebra (node-form linear rules are named follow-up), or runtime enforcement;
traced-twin coherence and the executable finite-support checker are the named
v6 lane.

Release inventory with audited theorem receipts:
[`docs/V5-RELEASE-LEDGER.md`](docs/V5-RELEASE-LEDGER.md).

## 4.0.0 — Custody-Indexed Sequents

*A Lean proof release for custody-aware authority semantics.*

**v4.0.0 introduces a parameterized indexed-sequent skeleton** — the proof
discipline for how the v3 lifecycle calculi may be *crossed* without silently
erasing custody. The campaign modules live under `LeanProofs/Scratch/`
(custody class SCRATCH, fenced, CI-covered as their own build target
`CustodyIndexedSequents` — build coverage, not promoted kernel authority).

What v4 proves:

- **structural read discipline is explicit** — context behavior is a system
  parameter, and contraction is *priced*: the same rule from the same single
  assumption derives under the Cartesian instance and is refused under the
  linear instance (`cartesian_contraction_free` / `linear_contraction_priced`
  / `linear_pay_twice`);
- **bridge composition preserves provenance** — a composed crossing carries
  every hop's evidence; nothing is fused or forgotten
  (`composition_cannot_erase_bridge_evidence`);
- **index connectivity does not imply derivability** — bridges connect
  *judgments*, not indices; a mismatched midpoint kills the composite even
  when the index graph says "connected";
- **route provenance matters** — two routes to the same target carry distinct
  evidence chains, and an unfunded route stays closed;
- **master shapes are screened on both faces** — universal *indices*
  (`MasterFree`) and universal *evidence* (`EvidenceCurrencyFree`), each with
  a detection pair and honestly-named screening limits;
- **derived evidence cannot become universal bridge currency** — evidence may
  be produced by paid derivations, but funding never widens along derivation
  (*the rule relation is the sole authority map; derivation navigates it,
  never extends it*), and universality is inherited, never minted;
- **every cross-index derivation roots in read evidence whose original scope
  funded it** — the capstone `eentail_iff_read_rooted`: derivability is
  *equivalent* to read-rooted normal form. No custody chain, no derivation.

The central invariant remains: **no artifact may testify beyond the stage it
actually survived.**

v4 does not define a master `Admissible` judgment, does not introduce default
bridge transitivity, does not claim runtime enforcement, and does not claim
full Gentzen cut elimination — structural coverage is read discipline
(contraction/consumption), not the full structural-rule algebra. The explicit
follow-up is **v5: Custody-Preserving Normalization**.

Release inventory with audited theorem receipts:
[`docs/V4-RELEASE-LEDGER.md`](docs/V4-RELEASE-LEDGER.md).

## 3.0.0 — Bounded Lifecycle Calculi

*A Lean proof release for custody-aware authority semantics.*

**v3.0.0 completes the bounded lifecycle-calculi family.** The central invariant:

> **No artifact may testify beyond the stage it actually survived.**

v3 models this invariant across nine local, bounded judgment systems
(`LeanProofs/BoundedCalculi/`, custody class ANNEX — release surface, not
promoted kernel authority):

- **Temporal Custody** — valid then does not imply valid now.
- **Surface / Projection** — rendered or summarized does not imply authorized.
- **Refusal / Denial** — silence or displayed refusal does not imply valid denial.
- **Boundary Artifact** — internal evidence does not imply external mint authority.
- **Obligation / Residue** — consumed resource does not imply obligations vanished.
- **Safety Preservation** — authorized steps do not imply safe trajectory.
- **Execution Custody** — ticket accepted or commit attempted does not imply
  successful execution (a stage-separation calculus, not an actuator model).
- **Boot / Genesis** — boot state does not imply root omnipotence; capability
  accumulation is staged and nested, not escalation, and there is no signed
  operator shortcut past discovery.
- **Checkpoint Settlement** — compacted history mints no new authority,
  discharges no unknown commit, and upgrades no observation to safety; live
  occurrences are conserved exactly.

**What v3 does not claim.** This is not a unified admissibility calculus:
there is no master `Γ ⊢ Admissible(a)` judgment. The aggregate import
(`LeanProofs/BoundedCalculi.lean`) establishes checkability and coexistence
only — not intercalculus coherence, not default bridge composition, not
runtime authority. Cross-calculus movement requires explicit bridge evidence,
and bridge composition is not transitive by default. Sequents, bridge
composition, and the broader custody-indexed sequent program are deferred to
the next campaign (v3.x scratch exists under `LeanProofs/Scratch/`, fenced,
named-not-claimed).

Release inventory with per-module theorem receipts:
[`docs/V3-RELEASE-LEDGER.md`](docs/V3-RELEASE-LEDGER.md). Campaign audit
trail: [`docs/CHANGELOG-scratch-campaign.md`](docs/CHANGELOG-scratch-campaign.md).
Lineage — Gentzen, linear logic, authorization logic, proof-carrying
code/authorization, TLA, PROV, IFC, scoped credentials, supply-chain
attestation — and what is distinct here: see *Relation to prior work* in
[`WHAT-THIS-PROVES.md`](WHAT-THIS-PROVES.md).
The umbrella architecture (Custody-Aware Authority Semantics) and the runtime
lanes (Bridge Foundry / compiled authority) live in the
[papers repo](https://github.com/unpingable/papers)'s ToolTheory roadmap; v3
is the Lean proof slice only.

## 2.0.0 — WDC: model-independent normalization and audit fence

**2.0.0** is the reserved WDC structural milestone: normalization is lifted from a
freshness-*model* theorem to a **model-independent admitting-class theorem**
(`normal_form_iff_of_commutes` over an explicit local commutation law, with a necessity
counterexample showing the law is load-bearing), and the repo gains a classifier-based audit
fence (axiom classes, native_decide policy, mathlib SHA pin — see [`docs/AUDIT-POLICY.md`](docs/AUDIT-POLICY.md)).
The public surface is **additive/non-breaking** — existing 1.x imports are unaffected; the
integer marks the reserved milestone, not an API break. See [`CHANGELOG.md`](CHANGELOG.md).

The **Witnessed Derivation Calculus** surface (the Mathlib-free
`LeanProofs.Witnessed.*` library, promoted in 1.4.0 and structurally strengthened in
2.0.0) provides:

- a witnessed-derivation judgment, `Lift`;
- paid composition and multi-context cut;
- a positive formula layer (`atom`, `top`, conjunction, disjunction) with explicit cut syntax and syntactic cut-elimination;
- a Gentzen-style single-succedent presentation with explicit left/right rules and soundness against the WDC-induced formula semantics;
- a canonical resource/residue layer with position-pinned validation and residue-preservation non-suppression;
- soundness, provenance, and revocation non-manufacture results (schematic);
- a model-independent normal-form factorization theorem over any admitting class
  satisfying the local commutation law, with the canonical freshness embedding as its
  public instance;
- a separate four-axis model-admission filter, `WitnessedDiscipline` (`bridge_valid` / `semantic_nontrivial` / `bridge_selective` / `properly_live`);
- a factorization showing the former `Discriminating` axis contributes no independent information beyond `SemanticNontrivial` under `BridgeValid`.

The name is deliberately narrow. This is **not** a process calculus, a maximal admissibility logic, or a unification of every kernel in the repository. The calculus governs witnessed derivation across typed bridges; the formula/Gentzen/resource additions are the positive presentation and canonical-residue slices only, not implication, full linear logic, or model-to-world transfer. `WitnessedDiscipline` is a model filter beside it, not part of normalization, and the 2.0 normalization result is an admitting-class theorem, not universal normalization.

The ratified calculus lives in the canonical surface as `LeanProofs.Witnessed.*` — a separate **Mathlib-free** library (`import LeanProofs.Witnessed`), with its axiom footprint regression-gated by `scripts/check-witnessed-footprint.sh`. Its ratified source is preserved under `experiments/no_free_lift_wiring/`. The public surface remains **additive/non-breaking** relative to 1.x; 2.0.0 is the structural WDC milestone, not an API churn release. The historical promotion gate is recorded in [`V2.0-EXIT-CRITERIA.md`](experiments/no_free_lift_wiring/V2.0-EXIT-CRITERIA.md); the post-v2 frontier is tracked in [`docs/WITNESSED-FRONTIER-REGISTER.md`](docs/WITNESSED-FRONTIER-REGISTER.md).

- **Exact ratified claims and theorem receipts:** [`RATIFICATION-v1.3.md`](experiments/no_free_lift_wiring/RATIFICATION-v1.3.md)
- **Migration and divergence constraints:** [`MIGRATION-NOTES.md`](experiments/no_free_lift_wiring/MIGRATION-NOTES.md)
- **2.0 release gate receipt:** [`V2.0-EXIT-CRITERIA.md`](experiments/no_free_lift_wiring/V2.0-EXIT-CRITERIA.md)
- **Downstream v2 consumer receipt:** [`downstream/wdc-v2-consumer/`](downstream/wdc-v2-consumer/)
- **Release:** `v2.0.0` (supersedes [`v1.4.0`](https://github.com/unpingable/lean/releases/tag/v1.4.0))

## Stable public surface: Admissibility Kernels

The stable public surface remains a collection of small admissibility kernels, each isolating a particular refusal boundary: stale authority, invalid standing upgrades, unauthorized transition, collapsed public surfaces, unwitnessed movement, and related category errors.

> Local kernels decide admissibility. Witnessed movement between contexts requires an explicit bridge.

The repository therefore contains two related but distinct layers:

1. **Admissibility Kernels** — small local refusal kernels (the stable 1.x public surface).
2. **Witnessed Derivation Calculus** — the ratified calculus for witnessed movement and composition across typed bridges, a canonical **Mathlib-free** surface (`LeanProofs.Witnessed.*`) shipped in 1.4.0 and structurally strengthened in 2.0.0.

Neither is a universal model of institutions, software systems, or agency.

## Start here

- **What changed in v1.3** → [`RATIFICATION-v1.3.md`](experiments/no_free_lift_wiring/RATIFICATION-v1.3.md)
- **Plain-English project explainer** → [`WHAT-THIS-IS.md`](WHAT-THIS-IS.md). No formal-methods background assumed.
- **A single kernel walked end-to-end** → [`docs/worked-examples/standing-upgrade-block.md`](docs/worked-examples/standing-upgrade-block.md). What it refuses and why.
- **What the current Lean stack proves** → [`WHAT-THIS-PROVES.md`](WHAT-THIS-PROVES.md)
- **Full admissibility-kernel reference** → [`LeanProofs/Admissibility/README.md`](LeanProofs/Admissibility/README.md)
- **Project root, author, full preprint list** → [unpingable.github.io](https://unpingable.github.io/). The [papers repo](https://github.com/unpingable/papers) is the prose home; this repo is the formal audit harness for the Δt research series.

## How to read this repository

Most modules follow the same discipline:

1. define a small model of a boundary or failure surface;
2. state the invalid inference the system must not allow;
3. prove that the inference cannot be derived under that model;
4. leave implementation, policy, and world-level consequence outside the theorem.

The point is not to prove an entire software system correct. It is to make invalid promotions and unpaid boundary crossings mechanically visible before they become architecture.

## Map

- **Authority kernels** — authority, standing, verdicts, state transition, execution, corrective layers.
- **Surface / receipt / witness kernels** — collapsed surfaces, public receipt refinement, witness invariance.
- **Admissibility axes** — artifact kind, numerical kind, closure, recovery margin, freshness.
- **Cross-boundary artifact specimens** — exposure, degradation, failure minting, cascade.
- **Safety-bridge family** *(Frontier 1)* — proves that authorization does not entail defended-value preservation; a separate bridge predicate is required. Ratifies the standalone safety axis, not any unified-calculus rename.
- **Witnessed Derivation Calculus** *(ratified; canonical `LeanProofs.Witnessed.*` since 1.4.0, structurally strengthened in 2.0.0, Mathlib-free)* — witnessed movement and composition across typed bridges, now with the additive positive-formula and canonical resource/residue slices. See the release section above.

For the full module-by-module reference, see [`LeanProofs/Admissibility/README.md`](LeanProofs/Admissibility/README.md).

## Stable 1.x public surface

> **The Lean work did not produce a *unified* calculus. It produced a set of small admissibility kernels, each isolating a different refusal boundary — and, in v1.3, a narrow witnessed-derivation calculus beside them.**

The stable public surface (**Admissibility Kernels**, unchanged since 1.0) is a Lean authority kernel with typed verdicts and object-level refusal theorems for admissible transition. General composition rules and meta-theorems are out of scope for the 1.x stable surface and live in separate kernel families. Not a sequent calculus, not a process calculus, not a proof-theoretic admissibility logic, not a unified maximal calculus — see the scope fence in [`LeanProofs/Admissibility/README.md`](LeanProofs/Admissibility/README.md) for the full list of non-claims.

Importing `LeanProofs.Admissibility.AdmissibilityKernels` brings the eight stable modules into scope (`Authority`, `StateTransition`, `Derivation`, `Execution`, `Corrective`, `Freshness`, `SurfaceAuthorization`, `WitnessInvariance`). Seven specimen consumers live in `LeanProofs.Admissibility.Examples`, demonstrating the public API.

> Admissibility Kernels models when evidence-backed claims may authorize transitions, proves that boundary-crossing upgrades are impossible by construction, and refuses laundering across the surface, freshness, witness, and authority axes.

(Migration note: this aggregator was previously named `CalculusOne` under an "Admissibility Calculus 1.0" framing. The rename retires "calculus" from the *stable* public surface; the Witnessed Derivation Calculus reintroduces it only for that narrow witnessed-derivation object. Namespace `Admissibility.CalculusOne` is now `Admissibility.Kernels`; the marker theorem `calculus_one_compiles` is now `kernels_compile`. The deprecated import shim shipped through v9 and was removed in v10.0.0.)

## Repository custody and compatibility

Annex modules (recovery doctrine, cross-boundary specimens, numerical/artifact-kind axes, experimental composition, reachability/refusal adapters, safety-bridge family) and root-level consumer specimens (Paper 24/25, NQ-shaped modules) build green but are not part of the stable compatibility claim. Many `LeanProofs/Admissibility/` modules are wired into `LeanProofs.lean` for regression coverage; fenced UNRATIFIED-CANDIDATE / SCRATCH material may still build only when invoked directly. Wiring is build-coverage, not public-surface promotion — promotion lives in the `AdmissibilityKernels.lean` aggregator's import list. Per-file custody status is regression-checked via `scripts/check-custody-classes.sh`; per-module roles are tracked in [`LeanProofs/Admissibility/README.md`](LeanProofs/Admissibility/README.md).

### `experiments/` — tracked wiring witnesses (non-canonical)

The `experiments/` tree holds reproducible integration artifacts that are **not imported by the canonical proof surface** — each is its own Lake project with its own toolchain pin. A successful build under `experiments/` attests that the wiring checks; it does **not** promote any result into the relied-upon theorem surface (build-exit-0 is attestation of the math, never admission of a world claim). See [`experiments/README.md`](experiments/README.md) for the per-project custody contract (`EXPERIMENTAL-WIRING`).

Currently: `no_free_lift_wiring/` — the customs-office spine plus modeled freshness/authority embeddings. It hosts the **ratified source** of the Witnessed Derivation Calculus (`Successor/` + the `Wired` spine) — now promoted into the canonical surface as `LeanProofs.Witnessed.*` (this tree remains the provenance record, still not imported by the canonical surface) — and the **findings record for the retired composition-classification gate** ([`COMPOSITION-CLASSIFICATION-TARGET.md`](experiments/no_free_lift_wiring/COMPOSITION-CLASSIFICATION-TARGET.md) — the proposed exhaustive classifier was investigated and retired as the wrong target, not unproved). The public-surface promotion was governed by [`V2.0-EXIT-CRITERIA.md`](experiments/no_free_lift_wiring/V2.0-EXIT-CRITERIA.md): public promotion, migration map, stable namespace, and a non-experimental compiled consumer — not new theorems. That promotion shipped in 1.4.0; the 2.0.0 release is the later structural normalization + audit-fence milestone.

## What this is not

This is not a complete formal model of institutions, platforms, incidents, or distributed systems.

It is not a general-purpose process calculus.

When a theorem lands here, it means a specific invalid inference has been isolated tightly enough to be checked mechanically.

## Companion repos

- **Papers repo:** [`unpingable/papers`](https://github.com/unpingable/papers) — prose papers, working notes, primitives, and the research-program structure. The paper-side crosswalk at [`docs/formalization-index.md`](https://github.com/unpingable/papers/blob/main/docs/formalization-index.md) inverts this repo's view (paper → module).
- **This repo (Lean):** admissibility kernel modules, the witnessed-derivation calculus, the formal claim register for Δt-paper claims, proof attempts, corrected theorem statements, and the BROKEN / STALE / SOUND audit. Module → paper crosswalk lives in [`PAPER-MAP.md`](PAPER-MAP.md).

## Audit harness for the Δt framework

The audit-harness layer translates selected claims from the [Δt framework](https://github.com/unpingable/papers) into Lean so they can be checked against explicit definitions instead of persuasive prose. The framework's prose papers make claims about how complex systems degrade, recover, misread themselves, or substitute proxies for reality. It is one consumer of the admissibility kernels, not the whole repo.

Some claims survive. Some narrow. Some break.

That is the point. Lean is used here as a pressure chamber for theory: it helps distinguish structural claims from slogans that were useful for discovery but too loose to carry formal weight. Failed claims are kept as evidence of where the original prose overreached — see [`CLAIM-REGISTER.md`](CLAIM-REGISTER.md) for the BROKEN / STALE / SOUND / OPEN audit. The repo's value is less the surviving theorems than the disciplined damage report on the rest.

### Paper-anchored modules

**`LeanProofs/TaxonomyGraph.lean`** — Formal encoding of the cybernetic failure taxonomy (15 domains, 14 primitive + 1 composite). Encodes the pipeline graph, role classifications, and reinforcing loops as separate relations. Proves reachability, terminality, role distinctness, and decomposition claims. Cashes out into Paper 15 (sharpen + expose looseness), with secondary tie-ins to P16 and P22.

**`LeanProofs/BranchSelector.lean`** — Dual-budget closure-family selection. Budget asymmetry / priming / susceptibility. Cashes out into Paper 9 (certify + sharpen).

**`LeanProofs/PersistenceModel.lean`** — Five-state Δc→Δh dynamics. Cumulative rollback depletion under detached commits; three-way recovery distinction. Quantitative-burn + trace-realization cluster (added 2026-05-08): closed-form `commitsToHysteretic` commit count; non-strict and strict commit-count monotonicity (strict requires positive capacity above the per-commit burn unit); realization bridge from closed-form arithmetic to actual `run`-trace semantics; trace-level *post-repair faster* doctrine theorem composing the strict inequality with two applications of the realization bridge. Cashes out into Paper 18 (sharpen + bridge; Appendix A v1.1 candidate).

**`LeanProofs/OpsMasking.lean`** — Operational masking, case (i) projection clause. Pointwise-equal projected actions produce identical trajectories. Cashes out into Paper 23 (bridge + certify).

**`LeanProofs/Paper24SharedVision.lean`** — Algebraic shard for Paper 24's §4 metric probes. Sign correction on Proposition 2.

**`LeanProofs/RepairOperator.lean`** — Sovereign repair operator. No paper anchor; formalizes the working note `working/sovereign-repair-operator.md`.

**`LeanProofs/Admissibility.lean`** — P27 obligation skeleton (namespace `P27`). Sorry-free as of 2026-05-01 (three real proofs against the local `admissible` definition; two `True`-placeholder discharges with deferred-real-statement docstrings pending substrate-accusation / causal-binding predicates). Intentionally **not** wired into `LeanProofs.lean` root. Sibling but independent from the `Admissibility/*` kernel modules; the P27 skeleton is post-transition obligation accounting, the kernel is pre-action authorization.

### First documented BROKEN claim

The audit's first recorded finding, kept here as the chronological anchor for the BROKEN/STALE/SOUND register. Subsequent results — the Admissibility Kernels surface, the sorry-free kernel chain, and the cross-boundary specimens — are tracked in [`WHAT-THIS-PROVES.md`](WHAT-THIS-PROVES.md) and [`CLAIM-REGISTER.md`](CLAIM-REGISTER.md); gaps against the AGI-requirements doc live in [the closed 2026-05-10 reverse-gap audit](historical/audits/AGI_REQUIREMENTS_REVERSE_GAP_AUDIT_2026-05-10.md). Not appended here.

**(2026-04-02; refined 2026-06-29):** The informal claim "Δh is the universal sink" is false as a pipeline reachability claim. Δs and Δk cannot reach Δh through pipeline edges; the static graph instead decomposes into three terminal closure families `{Δg, Δa}`, `{Δx}`, `{Δh}` (Δh is *a* terminal family, not *the* sink). Any "universal sink" reading of Δh would be a *temporal-attractor* claim rather than a graph-topological one — and that temporal claim is **OPEN**: it requires an explicit dynamics substrate the static graph cannot represent (the placeholder axiom that once stood in for it was removed in v2.0.0). The prose was compressing two different kinds of claims into one sentence. See [`CLAIM-REGISTER.md`](CLAIM-REGISTER.md) #1 for the full status.

## Building

Requires [elan](https://github.com/leanprover/elan) and Lean 4.

```bash
lake build                  # Mathlib-free custody/release surfaces incl. ViewSemantics candidate/application targets
lake build Witnessed        # the Witnessed Derivation Calculus in isolation (Mathlib-free)
bash scripts/check-witnessed-footprint.sh   # re-attest the ratified WDC axiom footprint (fail-closed)
bash scripts/check-viewsemantics-footprint.sh # candidate theorem/checker footprints (fail-closed)
bash scripts/check-viewsemantics-isolation.sh # cheap roots Mathlib-free; P25 isolated
bash scripts/audit-axioms.sh                # repo axiom classifier (signature/interface-law/specimen; 0 forbidden)
bash scripts/audit-native-decide.sh         # native_decide confined to finite-witness modules
bash scripts/check-mathlib-pin.sh           # lakefile mathlib rev == manifest SHA (no silent drift)
```

The ViewSemantics campaign remains `UNRATIFIED-CANDIDATE`: the v10 release
archives the tree, and neither the tag/DOI nor default build coverage is a
custody promotion. Its P25 adapter remains outside the default cheap graph and
builds explicitly with `lake build ViewSemanticsMathlibIslands`.

**Custody posture: the repository is not axiom-free; it is *axiom-classified*. WDC promoted
receipts remain footprint-attested.** See [`docs/AUDIT-POLICY.md`](docs/AUDIT-POLICY.md) for
what each gate checks and the four axiom classes (signature / interface-law / specimen /
forbidden — the last held at zero).

The ratified source of the calculus also builds standalone under
`experiments/no_free_lift_wiring/` (its own Lake project / toolchain pin) — that tree
is the provenance record, not the canonical import path.

## Cross-references

- [`LeanProofs/Admissibility/README.md`](LeanProofs/Admissibility/README.md) — full module-by-module reference for the admissibility kernel modules
- [`WHAT-THIS-PROVES.md`](WHAT-THIS-PROVES.md) — module-level exposition of what each proof establishes and what it rules out
- [`historical/audits/AGI_REQUIREMENTS_REVERSE_GAP_AUDIT_2026-05-10.md`](historical/audits/AGI_REQUIREMENTS_REVERSE_GAP_AUDIT_2026-05-10.md) — **closed audit artifact**: the dated 2026-05-10 AGI-requirements reverse-gap audit (gaps where *that one requirements document* demands more than the kernel delivers). Not the project's live open-problems register, not a promotion queue.
- [`PAPER-MAP.md`](PAPER-MAP.md) — module → paper crosswalk (which Lean modules cash out into which preprints, and whether the mapping is paper-ready)
- [`CLAIM-REGISTER.md`](CLAIM-REGISTER.md) — claim-level audit with specific prose-location status (BROKEN / STALE / SOUND / OPEN)
- [`RATIFICATION-v1.3.md`](experiments/no_free_lift_wiring/RATIFICATION-v1.3.md) — the ratified v1.3 claims with exact theorem receipts
- [`V2.0-EXIT-CRITERIA.md`](experiments/no_free_lift_wiring/V2.0-EXIT-CRITERIA.md) — release-gate receipt for the 2.0 boundary
- [`downstream/wdc-v2-consumer/`](downstream/wdc-v2-consumer/) — separate Lake consumer pinned to `v2.0.0`
- Narrative walkthrough: [`docs/worked-examples/standing-upgrade-block.md`](docs/worked-examples/standing-upgrade-block.md)
- Papers repo: [`docs/formalization-index.md`](https://github.com/unpingable/papers/blob/main/docs/formalization-index.md) — paper → module inverse view

## Status

**`v2.0.0` released** — the Witnessed Derivation Calculus now has model-independent admitting-class normalization and an explicit audit fence, while the stable 1.x Admissibility Kernels surface remains unchanged. All root-imported modules build. **Sorry-free as of 2026-05-28.** No theorems are currently admitted via `sorry`. Gaps surfaced by the dated 2026-05-10 AGI-requirements reverse-gap audit are recorded in [the closed reverse-gap audit](historical/audits/AGI_REQUIREMENTS_REVERSE_GAP_AUDIT_2026-05-10.md) — a **closed audit artifact** scoped to that one requirements document, not the project's live open-problems register.

The previously-admitted investigative null `corrective_then_forward_is_not_monotone` (formerly in `LeanProofs/Admissibility/Corrective.lean`) was replaced by a positive boundary result in `LeanProofs/Admissibility/CorrectiveBoundary.lean`: the abstract kernel's existential remains formally undecidable in current vocabulary, but a parallel miniature kernel exhibits both possible answers — identity store ops + arbitrary env make the existential FALSE; nondegenerate ops + verdict-sensitive derivation make it TRUE. The abstract kernel is consistent with both, which is the doctrinally-correct stance. See [`CLAIM-REGISTER.md`](CLAIM-REGISTER.md) entries A1 (resolved) and #14 (boundary result) for the audit trail. **The discipline that previously displayed the sorry now displays the resolution path** — admitted-statement history is part of the public record, not erased once resolved.

Other open questions — what the kernel does *not* yet rule out — are tracked alongside the proofs themselves: `CorrectiveMonotone` is currently vacuously satisfiable at the abstract kernel level pending behavioral laws on `applyUpdate` / `appendGap` / `appendRevocation` (the boundary module supplies the model-dependence story without forcing the abstract kernel to commit); environment mutation (replacing the evaluator rather than the state) is a separate laundering vector outside `WeaklyLessPermissive`'s scope. See [`NOTES.md`](NOTES.md) and the per-module pinned-questions blocks for the rest.

## Reading the proofs

This repository is the canonical formal source. Required CI verifies that the formalization builds (`lean-action` on push); proof correctness rests on the Lean source itself, not on any rendered artifact.

The human-readable entry point for proof readers is this README plus the companion documents linked under *Cross-references* above.

The papers-side companion at `docs/formalization-index.md` in the [papers repo](https://github.com/unpingable/papers) inverts the view (paper → module).

GitHub Pages renders this README at <https://unpingable.github.io/lean/> via classic Pages, so the proof reader's portal is reachable from the web without additional infrastructure. Generated `doc-gen4` API HTML is not currently published; if added later it will sit as a secondary reference layer beneath the human-readable portal, not as the front door.
