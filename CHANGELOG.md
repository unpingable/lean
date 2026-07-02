# Changelog

Release history for **Admissibility Kernels** (Lean stack). Versions correspond
to Zenodo deposits under the concept DOI
[10.5281/zenodo.20369489](https://doi.org/10.5281/zenodo.20369489); the GitHub
**release creation** (not the tag alone) mints the version DOI and drives the
deposit. Versions prior to 1.2.0 are recorded on Zenodo.

## 7.0.0 — Artifact Authority Profiles (2026-07-02)

*A Lean proof release for custody-aware authority semantics.*

7.0.0 proves the profile discipline: **profiles are local, crossings are
paid, receipts are not fungible across obligations, and coverage cannot be
minted.** Local profiles do not compose for free — holding two profiles'
local material is not holding their cross-profile authority
(`profile_does_not_compose_for_free`); conversion requires a declared paid
bridge receipt, with which the crossing composes
(`cross_profile_conversion_requires_bridge`). Stage ascent pays each rung:
a stage-n profile does not authorize stage n+1
(`profile_stage_noncollapse`), and any ascent holds every intermediate rung
receipt in custody at any derivation depth (`ascent_pays_every_rung`). The
generic evidence-jurisdiction screen (`JurisdictionRespecting`, minted on a
two-instance family repeat, per-vocabulary and local) makes receipt species
non-fungible: the prior local walls are recovered as exact instances (two
iffs), receipt cross-use is caught, and the once-escaped relation-promotion
attack is caught (`relation_promotion_fails_jurisdiction_screen`). Coverage
cannot be minted: derived evidence funds no obligation its origin could not
fund (`derived_evidence_covers_no_more`), and in single-scoped frames
covering k distinct obligations costs k distinct held receipts
(`coverage_costs_receipts`, with an exact-price witness). Coverage through
custody is legitimate when paid — the theorem is *no bulk discount*, not
suspicion of broad custody. **Non-claims:** no shared custody language (no
"Constellation Custody Protocol"); no master profile or universal schema
(the master screen's own false positive is demonstrated in-release); no WLP
semantics (envelope-only, untouched); no runtime/JSON/AG integration; no
profile registry; no issuer-level provenance-correlated portfolio
accounting (the named v7.x remainder); no graded "too much coverage"
policy screen. Screening, not enforcement. All modules `Custody-Class:
SCRATCH`, CI-covered; footprints ≤ [propext, Quot.sound], no
`Classical.choice`. Release inventory:
[`docs/V7-RELEASE-LEDGER.md`](docs/V7-RELEASE-LEDGER.md).

## 6.0.0 — Finite Custody Checking (2026-07-02)

*A Lean proof release for custody-aware authority semantics.*

6.0.0 makes the v5 payment discipline finitely checkable. A Lean-native
checker takes a liberal derivation tree and a finite context and returns a
typed result — `ok` with a positional occurrence trace, or a typed refusal
naming an offender (`CheckResult`; no bare Bool on the final surface). The
checker is **sound** (`check_ok_sound`/`checkCtx_ok_sound`: ok implies a
valid linear derivation over the given context, with read-spine,
position-distinct, context-provenant trace) and **complete**
(`check_complete`) — a decision procedure, not a semi-decision — and its
verdict is decided by finitely many count comparisons over the read spine
(`firstDeficient_decides_check`), closing the executable finite-support
boundary v5 explicitly left unclaimed. Refusals are never mislabels: the
offender's total demand genuinely exceeds supply
(`check_refusal_excess`), and the offender is genuinely demanded. Beneath
the checker, **traced and untraced normalization provably agree** — same
verdicts, the same offender on refusal, residuals equal up to label
projection (`tracing_preserves_verdicts`, `linearizeT_ok_projects`,
`linearizeT_forgery_projects`): tracing is testimony about payment, never a
change to who gets paid. The canonical tagging bridge
(`untraced_runs_trace_canonically`) lifts any plain-context run to a traced
run at zero semantic cost. The resident C2 screen layer
(`DecidableScreens`) is claimed into this release surface: executable Bool
screens with soundness iffs against the v4 Prop screens — screening as
computation, soundness as theorem. **Non-claims:** not a CLI, not a runtime
checker, not Bridge Foundry, not an artifact profiler; not a derivability
decision procedure (checks a given tree; no proof search); not a checker
for arbitrary future structural systems; not a master admissibility layer;
offender identity across the two refusal reporters not claimed. All modules
`Custody-Class: SCRATCH`, CI-covered; footprints ≤ [propext, Quot.sound],
no `Classical.choice`. Release inventory:
[`docs/V6-RELEASE-LEDGER.md`](docs/V6-RELEASE-LEDGER.md).

## 5.0.0 — Custody-Preserving Normalization (2026-07-01)

*A Lean proof release for custody-aware authority semantics.*

5.0.0 delivers the normalization layer for the v4 sequent skeleton, with the
custody inversion as its thesis: **classical normalization removes detours
and preserves derivability; custody-preserving normalization removes only
policy-licensed detours and refuses when removal would erase payment.** A
liberal structural derivation normalizes into the custody discipline **iff**
its reads can be paid by occurrences — per-label occurrence counting decides
normalization exactly (`linearize_ok_iff_counts_suffice`); refusal is a typed
forgery whose named offender is itself a genuine excess-demand witness
(`forgery_offender_is_excess`). Successful normalization conserves
occurrences for every measure (`linearize_ok_conserves`), preserves the
custody chain (`chainOf_linearize`), and carries a positional occurrence
trace proving **who paid**: each read funded by a distinct original-context
occurrence, no occurrence paying twice, nothing paying that was not there
(`OccurrenceTrace`). The same liberal syntax, priced by two disciplines, gets
two verdicts: Cartesian derives, linear refuses
(`cartesian_statable_but_linearly_refused`). The starting point is made
honest by the already-normal theorem (`all_derivs_read_rooted`): under the v4
discipline there are no cut redexes — the detours v5 prices are structural
(weakening/contraction/exchange), entering as explicit nodes
(`StructuralNormalization`). **Non-claims:** not full Gentzen cut
elimination; not a full structural-rule algebra (node-form linear rules are
named follow-up); not runtime; traced-twin coherence and the executable
finite-support checker are v6 lane. All modules `Custody-Class: SCRATCH`,
CI-covered, ≤ `[propext, Quot.sound]`, per-slice adversarial audits; see
`docs/V5-RELEASE-LEDGER.md`.

## 4.0.0 — Custody-Indexed Sequents (2026-07-01)

*A Lean proof release for custody-aware authority semantics.*

4.0.0 introduces a **parameterized indexed-sequent skeleton**: the proof
discipline for crossing the v3 lifecycle calculi without silently erasing
custody. Generalizes the post-v3 sequent ladder (S0–S4) into a proof theory
where: structural **read discipline is explicit** (contraction priced across
Cartesian and linear context instances — one rule, one assumption, derivable
under one policy and refused under the other); **bridge composition preserves
provenance** (`composition_cannot_erase_bridge_evidence`); **index
connectivity does not imply derivability** (bridges connect judgments, not
indices); **route provenance matters** (diamond instance; unfunded routes stay
closed); **master shapes are screened on both faces** (`MasterFree` for
universal indices, `EvidenceCurrencyFree` for universal evidence stamps, each
with a detection pair and named screening limits); and **derived evidence
cannot become universal bridge currency** (funding never widens along
derivation; universality is inherited, never minted). The capstone,
`eentail_iff_read_rooted` (zero-axiom): derivability with derived evidence is
EQUIVALENT to read-rooted normal form — every cross-index derivation roots in
read evidence whose original scope funded it.

Custody: the campaign modules (`BridgeSequent`, `ExecutionSequent`,
`ExecutionObligationSequent`, `BridgeCompositionSequent`,
`CustodyIndexedSequent`, `StructuralPolicySequent`,
`EvidenceCalculusSequent`) remain **Custody-Class: SCRATCH** — fenced sequent
discipline, not promoted kernel authority — and are CI-covered as their own
build target (`CustodyIndexedSequents`; build coverage ≠ promotion).
`LeanProofs.lean` unchanged. No master `Admissible`; no default bridge
transitivity; no runtime claim; structural coverage is read discipline, NOT
the full structural-rule algebra; **full Gentzen cut elimination is not
claimed** — the explicit follow-up is v5: Custody-Preserving Normalization.

Inventory with audited theorem receipts: `docs/V4-RELEASE-LEDGER.md`. Campaign
trail: `docs/CHANGELOG-scratch-campaign.md`.

> v3 proved the family. v4 proves the family can be crossed without silently
> erasing custody.

## 3.0.0 — Bounded Lifecycle Calculi (2026-07-01)

*A Lean proof release for custody-aware authority semantics.*

3.0.0 completes the **bounded lifecycle-calculi family**: the six existing
ANNEX bounded calculi (TemporalCustody, SurfaceProjection, RefusalDenial,
BoundaryArtifact, ObligationResidue, SafetyPreservation) are joined by three
promoted family members — **ExecutionCustody** (stage separation: ticket
accepted / commit attempted / executed / safe / discharged do not collapse),
**BootKernel** (genesis: witnessed settlement, anti-skip wall, no signed-root
shortcut, accumulation-is-not-escalation), and **CheckpointSettlement**
(occurrence-linear compaction: mints nothing, conserves live multiplicity,
discharges no unknown commit, upgrades no observation to safety) — plus
`MeasureAccounting` (generic conservation engine, support module).

Promotion custody: Scratch → `BoundedCalculi/` ANNEX **release surface** by
operator decision 2026-07-01. **No promoted kernel/import boundary changed**:
`LeanProofs.lean` imports neither `BoundedCalculi` nor `Scratch`; the aggregate
`BoundedCalculi.lean` remains a compile marker (checkability/coexistence only —
not coherence, not composition, not global admissibility). There is **no master
`Admissible` judgment** and no default bridge transitivity.

Deferred, named-not-claimed: **custody-indexed sequents** (v3.x campaign;
Sequents 0–3 exist as fenced scratch under `LeanProofs/Scratch/` — indexed
bridge cut, zero-axiom syntactic no-free-cross-cut, execution-ticket linear
sequent, obligation/receipt books; Sequent 4, bridge composition, unbuilt by
design) and the longer-horizon custody-indexed Gentzen system (v4, if earned).

Gate record: full build green; `audit-axioms` / `audit-native-decide` /
`check-mathlib-pin` / `check-witnessed-footprint` all exit 0; no
`sorry`/`admit`; footprints ≤ `[propext, Quot.sound]`, re-attested post-move.
Inventory: [`docs/V3-RELEASE-LEDGER.md`](docs/V3-RELEASE-LEDGER.md). Campaign
trail: [`docs/CHANGELOG-scratch-campaign.md`](docs/CHANGELOG-scratch-campaign.md).

> v3 proves the family. v3.x starts proving the crossings.

## 2.0.0 — WDC: model-independent normalization and audit fence (2026-06-29)

2.0.0 promotes Witnessed Derivation Calculus normalization from a freshness-*model* theorem
to a **model-independent admitting-class theorem**, and hardens the repo's custody fence.

**On the version.** This major bump marks the *reserved* WDC structural milestone — 1.4.0
deliberately spent a minor "to leave the integer 2.0 owed" for exactly this proof-theoretic
strengthening (criterion #1 in `docs/WITNESSED-FRONTIER-REGISTER.md`), which has now landed.
The public surface is **additive / non-breaking**: existing 1.x imports are intended to
remain unaffected — `bridge_path_normal_form` keeps its name, signature, and `[propext]`
footprint. The integer marks the milestone, not an API break.

### WDC 2.0 — the structural theorem

- **`LeanProofs/Witnessed/AbstractNormalization.lean`** — `normal_form_iff_of_commutes`
  (**axiom-free**): the carry-then-weaken normal-form factorization holds for ANY two-family
  paid bridge satisfying the local commutation law `Commutes C W`, independent of the
  freshness model `(Nat, <, b−a)`.
- **`LeanProofs/Witnessed/CommutesNecessity.lean`** — `commutes_is_necessary` (**axiom-free**):
  the commutation law is load-bearing — a concrete system where it fails admits a paid path
  with no carry-then-weaken factorization. The theorem is genuinely conditional.
- **`Normalization.bridge_path_normal_form` rerouted** to be the `(CarryStep, WeakenStep)`
  instance of the abstract theorem (`perm_weaken_carry` discharges `Commutes`). Name,
  signature, and `[propext]` footprint **unchanged**. Prose: "canonical form" →
  "normal-form factorization" (existence of the split, not a unique canonical representative).

### Audit fence (see [`docs/AUDIT-POLICY.md`](docs/AUDIT-POLICY.md))

> **The repository is not axiom-free; it is axiom-classified. WDC promoted receipts remain
> footprint-attested.**

- **Footprint gate hardened** (`scripts/check-witnessed-footprint.sh`): `set -euo pipefail`,
  explicit failure if the `lake env lean` probe fails; 12 ratified receipts attested.
- **Repo axiom classifier** (`scripts/audit-axioms.sh` + `axiom-policy.tsv`): every
  `axiom`/`constant` classified — 23 signature, 0 interface-law, 8 specimen, **0 forbidden**,
  0 unclassified.
- **native_decide classifier** (`scripts/audit-native-decide.sh`): confined to finite-witness
  modules; forbidden in WDC / kernels / structural receipts.
- **mathlib pinned** in `lakefile.toml` to the manifest SHA, with a drift gate
  (`scripts/check-mathlib-pin.sh`). Moving mathlib is now explicit.

### TaxonomyGraph

- **Removed the `persistence_normalizes` placeholder axiom** (a `True`-bodied claim-shaped
  stand-in) — demoted to a non-asserting `TemporalAttractorSubstrate` socket. It was the lone
  forbidden axiom; the repo axiom census is now 0 forbidden.
- **Downgraded the unconditional temporal Δh claim to OPEN** (CLAIM-REGISTER #1): static
  topology neither proves nor refutes it; a conditional version needs an explicit dynamics
  substrate.
- **Promoted the static closure-partition result** as the headline: `{Δg, Δa}`, `{Δx}`, and
  `{Δh}` are three distinct terminal closure families under the declared edge graph. Δh is
  *a* terminal family, not *the* universal sink.
- **Edge-policy sensitivity**: `no_reach_of_closed_lane` (axiom-free) packages the negative
  result as "src inside a forward-closed lane, dst outside ⇒ unreachable"; fenced
  counterfactual edges (`Δm→Δc`, `Δx→Δc`) prove the static result FLIPS under one admitted
  handoff edge — i.e. it is edge-policy-relative, not universal over all policies.

### Boundary / Admissibility

Boundary-related reachability work in this release is **supporting infrastructure, not the
reason for the 2.0 integer**. It claims no Boundary composition *calculus*, no trichotomy,
and no exhaustiveness theorem; `RefusedByClosedLane ⇒ ¬Composable` is proved in one
direction only. A Boundary milestone, if earned later, gets its own name.

### Experimental / scratch (not part of the promoted surface)

- A **quarantined Persistence Attractor roadmap** (`experiments/persistence_attractor/NOTES.md`)
  and scratch packaging (`LeanProofs/Scratch/PersistenceAttractor.lean`, unimported, no
  axiom/sorry/native_decide). **No dynamic Δh theorem is claimed in this release.**

### Compatibility

Major version marks the reserved WDC structural milestone. Existing 1.x public imports are
intended to remain unaffected; the theorem surface is additive/non-breaking.

## 1.4.0 — Witnessed Derivation Calculus (2026-06-27)

1.4.0 promotes the ratified Witnessed Derivation Calculus into the **canonical public
surface** as the Mathlib-free `LeanProofs.Witnessed.*` library — no longer only under
`experiments/`. Supersedes `v1.3.0-rc1`. The stable 1.x Admissibility Kernels surface is
untouched.

**On the version.** The project's planning docs frame this as "the 2.0 boundary"
(`V2.0-EXIT-CRITERIA.md`), and it ships as **1.4.0** on purpose. Semver is a consumer
contract: this release is purely additive — nothing in the 1.x surface breaks — so it is a
**minor** bump, not a major one. The milestone (a second ratified formal object lands in
the public surface) gets its volume here and in the release title, not in the integer. A
future **2.0** is reserved for a *structural* strengthening of the calculus — see the
"What Would Make This 2.0" gate in
[`docs/WITNESSED-FRONTIER-REGISTER.md`](docs/WITNESSED-FRONTIER-REGISTER.md).

- **A1 — enforced Mathlib-free boundary.** New `Witnessed` `lean_lib` in `lakefile.toml`
  (`roots = ["LeanProofs.Witnessed"]`). No module under `LeanProofs/Witnessed/` imports
  Mathlib, so `lake build Witnessed` cannot reach it — the axiom-footprint cleanliness is
  build-graph-enforced, not merely re-checked.
- **Port.** The 12-module ratified cone (7 spine + 5 successor) copied from
  `experiments/no_free_lift_wiring/{Wired,Successor}/` into `LeanProofs/Witnessed/`,
  namespaced `LeanProofs.Witnessed.*`, wired into `LeanProofs.lean` (default target).
  Renames: `Wired.Authority` → `AuthorityModel` (study copy, kept off the `[1.0]`
  `Admissibility.Authority` name), `WitnessedDerivation` → `Derivation`, `Tightened` →
  `Discipline`, `DisciplineObstruction` → `Obstruction`, `tightened_metatheory` →
  `discipline_metatheory`. The experiment tree is unchanged and remains the provenance
  record (copied, not moved). Receipt names otherwise frozen.
- **Gate 4 — external consumer.** `LeanProofs/Witnessed/Examples.lean` imports only the
  canonical surface, builds a `Lift` derivation, and applies `no_free_lift` /
  `paid_lift_sound` — proving the promoted API is usable from outside the cone.
- **Gate 5 — footprint regression gate.** `scripts/check-witnessed-footprint.sh`
  re-attests all **10** ratified receipts against their documented footprints
  (`RATIFICATION-v1.3.md`): 6 axiom-free, 2× `[propext]`, 2× `[propext, Quot.sound]`.
  Fail-closed — non-zero on build failure, footprint drift, or `sorryAx`.
- **Gate 6 — prose reconciled.** `README.md`, `WHAT-THIS-PROVES.md`, and the ported file
  headers updated to the canonical-surface state; the retired-maximal-`Admissibility
  Calculus` fence kept visible throughout. Frontier roadmap published as
  [`docs/WITNESSED-FRONTIER-REGISTER.md`](docs/WITNESSED-FRONTIER-REGISTER.md) (named, not
  started; includes the "What Would Make This 2.0" gate).

## v1.3.0-rc1 — Witnessed Derivation Calculus (candidate, 2026-06-17)

A **candidate** experiment surface (`experiments/no_free_lift_wiring/Successor/`,
EXPERIMENTAL-WIRING, NOT in `defaultTargets`). Public 1.0/1.2 surface untouched. The
canonical-surface promotion later shipped in **1.4.0** (above). After the original
`composition_classification` gate was retired (see the entry below), a *successor* was
developed and earned a narrow technical name. Claims + exact theorem receipts:
`experiments/no_free_lift_wiring/RATIFICATION-v1.3.md`.

### Earned (compiled, axiom footprints ≤ `[propext, Quot.sound]`, no `sorry`)
- **Witnessed Derivation Calculus** — the defined inductive judgment `Lift` with composition
  (`derivation_extends_along_paid_path`), genuine multi-context cut (`cut_admissible_general`),
  soundness (`paid_lift_sound`), provenance (`no_free_lift`), and non-manufacture
  (`revoked_floor_derives_nothing`) — all schematic — plus a canonical-form **normalization**
  theorem (`bridge_path_normal_form`) established **for the freshness embedding model**. The
  name is earned by exhibiting the full package in a canonical model, not by an abstract
  universal normalization theorem.
- **Four-axis model-admission discipline** `WitnessedDiscipline` (`bridge_valid` /
  `semantic_nontrivial` / `bridge_selective` / `properly_live`) — a filter BESIDE the
  calculus (`Normalization` never imports it). The earlier single `Discriminating` axis is
  retired by factorization: under `BridgeValid` it is exactly `SemanticNontrivial`
  (`bridgeValid_discriminating_iff_semanticNontrivial`); `bridge_selective` adds the genuine,
  `B`-dependent teeth it lacked. Inhabited by the canonical freshness embedding
  (`embedding_is_witnessed`).

### Does not change / does not claim
- Public 1.0/1.2 surface — unchanged. Name is the **narrow** witnessed-derivation object;
  "Admissibility Calculus" is **not** revived.
- Refusal legibility / continuation-bearing refusal (an external agent_gov frontier) is
  **future candidate** — no Successor theorem proves it.
- agent_gov correspondences are external **implemented-instance / convergent evidence**, not a
  verified reduction, and are **not** part of the ratification basis.

## v1.3.0-rc1 — composition gate prosecuted and retired (2026-06-17)

A **status correction**, not new public mathematics. The `composition_classification`
promotion gate named in v1.2.0 was attempted and adversarially reviewed (non-Claude,
source-grounded, over the quarry copy); the result is a *retirement* of that target, not
progress toward it.

### Findings (no public-surface change)
- Attempted and adversarially reviewed the proposed composition gate; semantic bridge
  validity does not support the intended exclusive classification (`naive_exclusivity_fails`).
- Retained as durable corrections: arbitrary-length paid-path transport (framed as
  transport, not a calculus) and the semantic-truth ⊬ derivational-reach separation.
- Corrected the bridge non-closure account (carry-then-weaken; the *path* is sound, the
  one-step *relation* is not closed).
- Demoted the reach-floor closure condition to ordinary graph reachability / ancestor
  coverage.
- Withheld the word *calculus*; no successor promotion criterion adopted.

### Does not change
- The **1.0 public theorem surface** and all its non-claims — *unchanged*.
- "Calculus of attestation boundaries" was already a *destination* claim, not a present
  one. It remains a destination only; the specific gate proposed to earn it is now retired
  rather than pending. Findings record: `experiments/no_free_lift_wiring/COMPOSITION-CLASSIFICATION-TARGET.md`.

## v1.2.0 — No Free Lift candidate annexes (2026-06-16)

A **semantic / governance release**, not new public mathematics. It adds fenced
candidate and experimental material — shipped with its naming boundaries already
corrected — and records a version boundary: the No-Free-Lift work establishes a
formal **theory of attestation boundaries**, **not yet a calculus**.

### Adds
- Fenced `UNRATIFIED-CANDIDATE` annexes in `LeanProofs/Admissibility/`:
  `NoFreeLift.lean` (the paid-bridge-closure spine) and `CarryLaws.lean` (the two
  coordinate cost laws). Axiom-free, **unwired** (not imported by `LeanProofs.lean`),
  committed `94df70e`.
- A fenced **`experiments/` tree** (`Custody-Class: EXPERIMENTAL-WIRING`, its own
  Lake project, not imported by the canonical surface) containing
  `no_free_lift_wiring/` — the spine wired to modeled freshness/authority
  embeddings — with its audit (`WIRING-AUDIT.md`) and a ratification template
  (`RATIFICATION-PENDING.md`) coupled to the code.
- `COMPOSITION-CLASSIFICATION-TARGET.md` — names the theorem
  (`composition_classification`) required to promote the work toward any future
  "calculus of attestation boundaries" claim.

### Changes (experimental wiring de-placarded before release; no proof changed)
- `Wired.Contraction` → `Wired.BudgetMonotonicity` (proves the *metric* budget law,
  not the structural contraction rule).
- `Wired.Composition` → `Wired.CoCompilation` (proves co-compilation `True`, not a
  composition result).
- `composition_builds` → `modules_cocompile`.
- Removed a `"calculus is legal for this object"` overclaim from the aggregator
  docstring. Old names retained only as provenance notes.

### Does not change
- The **1.0 public theorem surface** (`AdmissibilityKernels`, the eight `[1.0]`
  modules) and all its non-claims — *unchanged*. This release adds material; it
  does not correct any public-surface "calculus" drift, because there was none.
- Ratification status: nothing promoted.
- No present-tense "calculus" claim; no substructural claim; no substantive
  composition theorem.

### Status
- `No Free Lift` is **canonical-tracked / candidate**, not canonical-ratified.
- "Calculus of attestation boundaries" remains a **destination** claim, gated on
  `composition_classification` (theory → calculus → substructural → conditional
  model→world; see the target doc). The word is not earned yet.
