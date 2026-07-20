# v14 Readiness Ledger — Governed Admissibility Calculus

**Status: frozen campaign ledger.** This records the seven-rung admission
sequence from the `v13.0.0` baseline. All seven rungs were admitted, the
capital-C name was separately ratified, and the operator subsequently released
`v14.0.0`; see [`V14-RELEASE-LEDGER.md`](V14-RELEASE-LEDGER.md). Per-rung
nonclaims below remain preserved as admission-time fences. Baseline:
`v13.0.0`
(`54ffd53fa61d179b8b15f9195e877e1fefcfbd27`, 2026-07-17), the
custody-reconciliation release that made the repository capable of receiving
this campaign. The v13 tag remains the immutable campaign baseline; the
admission sequence itself performed no tag action.

## Release shape

v14.0.0's theme is the **Governed Admissibility Calculus**: the repository's
central claim moves from "several formal families and their refusal
boundaries" to "the indexed compositional system governing them." The
completed private campaign is promoted in dependency order, **one reviewed,
operator-ratified bundle per rung**; a rung's admission is not admission of
the next. The canonical campaign plan and rung packets live in the sibling
skunkworks
(`ADMISSIBILITY_CALCULUS_PROMOTION_CAMPAIGN_2026-07-17.md` and the per-rung
candidate packets).

| Rung | Content | Status |
|------|---------|--------|
| 1 | `Domains`/`Located` as shared public substrate in the `path-verdict` root | **ADMITTED 2026-07-17** (commit `538cf0b2ff2b`) |
| 2 | `GovernedFamily` signature and generic laws | **ADMITTED 2026-07-17** (commit `8b93d459…`) |
| 3 | Weathering and BoundedPaidReachability instances | **ADMITTED 2026-07-17** (commit `f0f31310…`) |
| 4 | Exact refusal-packet spine (`SpineEncoding`/`LosslessEncoding`) | **ADMITTED 2026-07-18** (commit `6c026d12…` + comment fix `9f24240d…`) |
| 5 | Indexed comparison framework (concrete ledger stays evidence) | **ADMITTED 2026-07-18** (commit `dc9c8df5…` + docs fix `ba7590af…`) |
| 6 | Stored-decision crossing and witnessed inhabitant | **ADMITTED 2026-07-18** (commit `41510aa9…` + comment fix `721c2c8c…`) |
| 7 | Origin/history-bound BreakGlass instance (terminal forcing instance) | **ADMITTED 2026-07-18** (commit `5a92e17a…`) |

**All seven rungs are admitted, and the terminal naming claim is
ratified.** The capital-C decision was deliberately NOT decided by
rung-7 admission; it was taken as its own reviewed act on 2026-07-18,
after custody closed — research-tree records
`ADMISSIBILITY_CALCULUS_RUNG7_TRANSFER_RECEIPT_2026-07-18.md` (custody
closure `62ac346b…`) and
`ADMISSIBILITY_CALCULUS_CAPITAL_C_RATIFICATION_2026-07-18.md` (the
naming act, `d5d5f2a9…`). The assembled public object is the
**Admissibility Calculus**. The naming ratification was not itself a release;
the operator later completed the separate release acts recorded in the v14
release ledger.

The recorded split rule did not fire: all seven rungs belong to the released
v14 semantic surface.

## Rung 1 — Domains/Located (admitted 2026-07-17)

**Source:** private skunkworks `Calculi/SeamPathVerdict/{Domains,Located}.lean`,
sanitized per the rung-1 candidate packet
(`ADMISSIBILITY_CALCULUS_RUNG1_DOMAINS_LOCATED_CANDIDATE_2026-07-17.md`):
imports narrowed to `Edges` only, the former private `ListReceipts` proof
dependency localized as private structural lemmas, and the positional-indexing
convenience layer removed from the stable surface.

**Review and ratification:** hostile public-side review 2026-07-17 verified
the dependency cone, the frozen theorem inventory, the axiom receipts, the
evidence-custody split, and an independently re-run normalized dry compile
against the untouched v13 tree; the operator ratified the bundle the same
day. The "sin"-vocabulary theorem names were reviewed and accepted as-is.

**Public diff (this bundle):**

1. `LeanProofs/Admissibility/PathVerdict/Domains.lean` — 7 definitions,
   24 exported theorems (functorial domain transport, the
   re-domaining-is-not-laundering lock, `Sum`-coproduct mixing).
2. `LeanProofs/Admissibility/PathVerdict/Located.lean` — carried-id core,
   12 exported theorems (erasure tether, completeness/soundness, pinpoint,
   relocation-is-not-repair).
3. Both imports added to the registered exact root
   `LeanProofs/Admissibility/PathVerdict.lean` (explicit operator-ratified
   promotion; the `PathVerdict` lake target stays rooted at that aggregate).
4. Two `STABLE-SURFACE path-verdict` rows in `scripts/public-custody.tsv`.
5. New fail-closed footprint gate `scripts/check-pathverdict-footprint.sh`
   (36 exact receipts), wired into CI beside the existing family gates.
6. Receipts: `CLAIM-REGISTER.md` entry #19, `AGENTS.md` verification counts,
   this ledger.

**Frozen axiom footprint:** 36 receipts — 35 axiom-free;
`mixed_compose_authority_iff` uses only `propext`. No `sorryAx`, no
`Classical.choice`, no `Quot.sound`, Mathlib-free.

**Custody accounting after rung 1:** 181 public Lean sources — 84
STABLE-SURFACE, 96 PUBLIC-EVIDENCE, 1 REPOSITORY-AGGREGATE, across ten
stable roots and 100 ownership relations (v13 baseline: 179/82/96/1, 98).

**Evidence custody (deliberately NOT transferred):** positional indexing
(`LocatedIndexingEvidence`), promotion-audit adverse specimens
(`DomainLocationPromotionAudit` — raw-`LocatedVerdict` fabrication,
duplicate-id pinpoint failure, noninjective merge limits), and the
cross-calculus crossing adapter (`LocatedCrossingAdapter`) remain in
skunkworks Scratch custody. The public surface is the owl, not the search
for the owl.

**Nonclaims:** rung 1 authenticates no locations, preserves no unique ids
under arbitrary composition, reflects no domain values through noninjective
maps, exposes no positional indexing, promotes no crossing checker, and
admits no later rung.

## Rung 2 — the governed-family signature (admitted 2026-07-17)

**Source:** private skunkworks
`Calculi/Scratch/CrossCalculus/Signature.lean`, sanitized per the rung-2
candidate packet
(`ADMISSIBILITY_CALCULUS_RUNG2_GOVERNED_FAMILY_CANDIDATE_2026-07-17.md`):
documentation/namespace sanitation only, no semantic change. The rung-1
public commit `538cf0b2ff2b88087fb6372ec45a6ba611a81db0` is the immutable
campaign baseline this rung builds on.

**Review and ratification:** hostile public-side review 2026-07-17 verified
the zero-import dependency cone, the frozen inventory (one structure of 10
fields, one derived definition, six theorems), all-axiom-free receipts, an
independently re-run `Admissibility.Calculus` dry compile in the public
environment, and an independently re-run Prop-squashing rejection probe
(`Witness := fun _ => True` / `Refusal := fun _ => False` both rejected by
the sort checker). The operator ratified with three pins:

1. **Namespace accepted with doctrine reconciliation.**
   `Admissibility.Calculus` is the stable namespace for the unified object
   being constructed; its presence does not declare the calculus completed
   or earned — that claim is gated on rung-7 ratification. The v10
   reservation note in `LeanProofs/Admissibility/README.md` is revised (not
   repealed): the earlier artifact did not earn the name; the term remains
   reserved for the object now under construction at this address.
   Establishing the namespace now avoids a gratuitous migration after later
   rungs depend on the shared signature.
2. **Theorem renamed before the freeze:** `no_erasing_check_is_faithful` →
   `no_claim_erasing_check_is_faithful`, in both the canonical skunkworks
   source and the public copy. The name now identifies the exact
   obstruction (claim-collapsing projections) rather than inviting a
   stronger folklore reading; the research tree keeps
   `full_claim_check_is_faithful` as the control that checking itself
   remains possible.
3. **Universe-0 fence accepted as written:** witness/refusal data live in
   `Type`, not `Prop`; the promoted signature is universe 0; universe
   polymorphism is a separately reviewed redesign; no transport claim to
   arbitrary universes. The fence is recorded in the module header, not
   encoded into names.

**Public diff (this bundle):**

1. `LeanProofs/Admissibility/Calculus/Core.lean` — the `GovernedFamily`
   structure (10 fields), derived `Authority`, six generic laws; zero
   imports.
2. `LeanProofs/Admissibility/Calculus.lean` — exact stable aggregate.
3. New Lake target `AdmissibilityCalculus`, Mathlib-free, default-built;
   registered in `scripts/public-targets.tsv`.
4. New exact root registered in `scripts/stable-surfaces.tsv`
   (owner key `admissibility-calculus`); both files registered
   `STABLE-SURFACE` under it in `scripts/public-custody.tsv`.
5. Aggregate imported from `LeanProofs.lean`.
6. New fail-closed footprint gate `scripts/check-calculus-footprint.sh`
   (6 exact receipts), wired into CI.
7. Receipts: `CLAIM-REGISTER.md` entry #20, `AGENTS.md` verification
   counts, the README doctrine revision, this ledger.

**Frozen axiom footprint:** 6 receipts, all axiom-free. No `propext`, no
`Classical.choice`, no `Quot.sound`, no `sorryAx`, no imports, Mathlib-free.

**Custody accounting after rung 2:** 183 public Lean sources — 86
STABLE-SURFACE, 96 PUBLIC-EVIDENCE, 1 REPOSITORY-AGGREGATE, across eleven
stable roots and 102 ownership relations (post-rung-1: 181/84/96/1, ten
roots, 100).

**Evidence custody (deliberately NOT transferred):**
`SignaturePromotionAudit.lean` (twelve axiom-free hostile receipts and the
faithful full-claim control), the Prop-squashing probe, the UC-1 hostile
corpus, instance fixtures, and campaign worksheets remain in skunkworks
Scratch custody. The Weathering, paid-reachability, and BreakGlass
instances are later-rung no-distortion evidence, not rung-2 imports.

**Nonclaims:** rung 2 proves no funnel, lossless encoding, composition
operator, comparison law, crossing, generic origin/history authentication,
generic obligation lifecycle, arbitrary-family decision engine, unbounded
reachability result, or runtime correspondence, and admits no later rung.
`Authority` intentionally forgets witness multiplicity.

## Rung 3 — Weathering and BoundedPaidReachability (admitted 2026-07-17)

**Source:** private skunkworks one-owner seams created by the mandated
pre-transfer sanitation (move, not copy), per the rung-3 candidate packet
(`ADMISSIBILITY_CALCULUS_RUNG3_WEATHERING_BOUNDED_PAID_REACHABILITY_CANDIDATE_2026-07-17.md`)
against exact baseline `8b93d459683602dfb497686283f082eaa53b9f36`:

1. mechanical rename `paidReachability` → `boundedPaidReachability` across
   every private consumer (zero stale references remain);
2. import-free `Calculi/EvidenceWeathering/Core.lean` now solely owns
   `Weather`, `canTestify`, `Disposition`, `Admissible`, and the six
   selected native receipts; the legacy parent retains `Weather.renew` and
   `renewed_may_rely` only;
3. import-free `Calculi/Scratch/LawfulPaidReachability/Native.lean` now
   solely owns `Run`, staged `Provenance`/`Resource`/`Warrant`/`State`/
   `Action`/`Step`, and `occurrence_provenance` (with a private membership
   helper); the residual Core retains counting, append/split,
   inversion/frame laws, and the `[propext, Quot.sound]`-bearing
   `no_admission_beyond_standing`;
4. the bounded fixtures and `LawfulFrom` moved from hostile custody into
   `ReachabilityInstance`, reversing the import chain — the hostile
   modules (`RetroCausalWarrant`, `EndpointCleanHistory`) now consume the
   adapter, and the promotion audit imports `EndpointCleanHistory`
   explicitly;
5. the full private tree rebuilt green (211 jobs) and unique ownership of
   every moved declaration was verified by search.

**Review and ratification:** hostile public-side review 2026-07-17
verified all 16 advertised receipts at their exact footprints, the
30-control audit (16 axiom-free + 14 `[propext]`), and the scope facts in
source (two-branch `decide`, admission-only canonical witness,
`claimed.paid = []`, empty obligations). The operator ratified all eight
pins: scope/name (`BoundedPaidReachability`/`boundedPaidReachability`),
admission/custody/obligation honesty, the hand-written two-case checker,
the four-file split, the native-API canonical-ownership freeze of `Run`/
`Provenance`/`Resource`/`Warrant`/`State`/`Action`/`Step`, the 16-receipt
freeze at 10 axiom-free + 6 `[propext]`, move-not-copy custody, and the
`187/90/96/1/11/106` accounting with no new root or target. One
documentation requirement was added at ratification: the public Weathering
adapter states explicitly that its `PLift (Admissible …)` witness is
subsingleton because this native judgment carries no receipt data.

**Public diff (this bundle):**

1. four stable sources under `LeanProofs/Admissibility/Calculus/Instances/`
   (two import-free Native modules, two governed-family adapters), each
   **normalized-source-equal** to its one-owner private seam — proven by a
   comment-stripped diff modulo only the declared import/namespace
   substitutions;
2. the existing Calculus aggregate imports the two instance leaves;
3. four `STABLE-SURFACE admissibility-calculus` custody rows;
4. the fail-closed Calculus footprint gate extended 6 → 22 exact receipts
   (existing CI wiring unchanged);
5. receipts: `CLAIM-REGISTER.md` entry #21, `AGENTS.md` counts, this
   ledger. No new Lake library, target, default target, owner key, or
   exact root.

**Frozen axiom footprint (rung-3 receipts):** 16 — 10 axiom-free, 6
exactly `[propext]`. No `Quot.sound`, no `Classical.choice`, no `sorryAx`,
Mathlib-free. The rung must not be summarized as axiom-free.

**Custody accounting after rung 3:** 187 public Lean sources — 90
STABLE-SURFACE, 96 PUBLIC-EVIDENCE, 1 REPOSITORY-AGGREGATE, across eleven
stable roots and 106 ownership relations (post-rung-2: 183/86/96/1, 102).

**Evidence custody (deliberately NOT transferred):**
`Rung3InstancePromotionAudit.lean` (30 controls), `RetroCausalWarrant`,
`EndpointCleanHistory`, the saturation engine and its examples, the
remaining lawful-paid-reachability campaign modules, `Weather.renew` and
renewal-history material, and the UC worksheets remain in skunkworks
custody. No private evidence module is a transitive import of the stable
root.

**Nonclaims:** rung 3 proves no general paid-reachability decidability, no
saturation or synthesized barrier, no claim domain beyond the two
fixtures, no successful payment or non-vacuous custody, no obligation
lifecycle, no Weathering truth/renewal semantics, no spine adapter
(rung 4), no BreakGlass claim, and no runtime correspondence.

## Rung 4 — the exact refusal-packet spine (admitted 2026-07-18)

**Source:** private skunkworks one-owner seams created by the mandated
rung-4 pre-transfer sanitation (move, not copy), per the rung-4 candidate
packet
(`ADMISSIBILITY_CALCULUS_RUNG4_EXACT_SPINE_CANDIDATE_2026-07-17.md`)
against exact baseline `f0f313107fa318637a4b58b8f014953dd988000c` and
private reconciliation Commit A
`a3937f3775b36ebb75c2716e65838d6e7d2881c0`:

1. the `WeatherObstruction` inductive moved, unchanged, into the
   import-free one-owner seam
   `Calculi/EvidenceWeathering/ObstructionVocabulary.lean`; the legacy
   `Obstructions.lean` (which imports Bases, PathVerdict Edges, and
   `ListReceipts`) imports the seam and retains every evaluator and law —
   the full module never enters the stable cone;
2. the combined `SpineInstances.lean` split into one-owner leaves
   `WeatheringSpine.lean` and `BoundedPaidSpine.lean`, with the old path
   left as a declaration-free compatibility aggregate for downstream
   Crossing/BreakGlass research;
3. all seven pre-freeze renames applied tree-wide with zero stale
   references (`weather_funnel_distinguishes_stale_and_retired`,
   `BoundedPaidObstruction`, `boundedPaidSpine`,
   `bounded_paid_funnel_sound_natively`,
   `bounded_paid_decide_from_bare_returns_exact_barrier`,
   `bounded_paid_bare_refusal_round_trip`,
   `bounded_paid_no_barrier_for_funded`); no stable alias under any old
   name;
4. full private tree rebuilt green (215 jobs); unique one-owner check for
   every moved declaration — pass.

**Review and ratification:** hostile public-side review 2026-07-18
verified all 23 advertised receipts at their exact footprints, the
constant-`Unit` collapse module (5 axiom-free adverse receipts), the
fresh 22-control audit (8 axiom-free + 14 `[propext]`) including the
decisive same-claim second-barrier control, and the `SpineInstances`
import contamination the sanitation exists to cut. The operator ratified
all eight pins: contract (dependent `RefusalPacket`, both inverse laws,
bare-versus-exact), vocabulary (one import-free `WeatherObstruction`
seam; `missingWitness` outside the governed refusal image), split/name
(four files, seven renames, no aliases), instance (partial Weathering
decoder, total identity paid decoder), receipt (23 at 18 axiom-free +
5 `[propext]`), evidence (collapse + audit stay private), dependency
(exact graph only), and accounting (no new root/target;
`191/94/96/1/11/111`).

**Public diff (this bundle):**

1. four stable sources — `Calculus/Spine.lean` (15 receipts; the
   campaign's first cross-root edge, importing public
   `PathVerdict/Core.lean`), `Instances/Weathering/Obstructions.lean`
   (vocabulary only, no theorem receipt),
   `Instances/Weathering/Spine.lean` (4 receipts), and
   `Instances/BoundedPaidReachability/Spine.lean` (4 receipts) — each
   **normalized-source-equal** to its one-owner private seam, proven by a
   comment-stripped diff modulo only the declared substitutions;
2. the existing Calculus aggregate imports both instance spine leaves;
3. four `STABLE-SURFACE admissibility-calculus` custody rows, plus
   `PathVerdict/Core.lean` becoming intentionally dual-rooted
   (`admissibility-calculus,path-verdict`) — the fifth new ownership
   relation;
4. the fail-closed Calculus footprint gate extended 22 → 45 exact
   receipts, and its two stale rung-2-only header comments corrected;
5. receipts: `CLAIM-REGISTER.md` entry #22, `AGENTS.md` counts, this
   ledger. No new Lake library, target, default target, owner key, exact
   root, or top-level import.

**Frozen axiom footprint (rung-4 receipts):** 23 — 18 axiom-free, 5
exactly `[propext]`. No `Quot.sound`, no `Classical.choice`, no
`sorryAx`, Mathlib-free. The rung must not be summarized as axiom-free.

**Custody accounting after rung 4:** 191 public Lean sources — 94
STABLE-SURFACE, 96 PUBLIC-EVIDENCE, 1 REPOSITORY-AGGREGATE, across eleven
stable roots and 111 ownership relations (post-rung-3: 187/90/96/1, 106).

**Evidence custody (deliberately NOT transferred):**
`LosslessEncodingCollapse.lean` (the permanent adverse receipt against
the superseded reason-only contract), `Rung4SpinePromotionAudit.lean`
(22 controls incl. the same-claim barrier specimen), the full Weathering
`Obstructions.lean` calculus, Comparison, Crossing, LocatedCrossing, the
BreakGlass spine and audits, and every campaign worksheet remain in
skunkworks custody.

**Nonclaims:** rung 4 proves no bare-encoding injectivity, no universal
exact encodability, no witness identity from `clean`, no authentication
by decodability, no cross-family comparison/composition/checking
(rungs 5–6), no BreakGlass claim (rung 7), no runtime serialization or
conformance, and no v14 declaration or capital-C completion.

## Rung 5 — the indexed comparison framework (admitted 2026-07-18)

**Source:** private skunkworks
`Calculi/Scratch/CrossCalculus/Comparison/Core.lean`, the zero-import
generic core of the revised rung-5 construction
(`ADMISSIBILITY_CALCULUS_RUNG5_INDEXED_COMPARISON_REVISED_CANDIDATE_2026-07-18.md`),
built to the ratified scope
(`ADMISSIBILITY_CALCULUS_RUNG5_SCOPE_RATIFICATION_2026-07-18.md`, with
enumeration addendum and the entries-not-modules correction) against
public baseline `9f24240d…` and private native baseline `b7782e10…`.

**Review and ratification:** the first rung-5 candidate honestly stopped
at REVISE on four hostile-audit blockers (no proof-carrying index, A1/A2
map mismatch, overstated capability claims, private-vocabulary
pre-promotion). The revised construction discharged all four
structurally: dependent `ComparisonLaw` selection makes a kind label
unstorable without its law; `DirectionalWithLossReceipt` binds
preservation and the collapsed pair to the same stored map;
`CapabilityDisposition` makes support-without-receipt generically
impossible; `JudgmentView` contains only a carrier and predicate, and
`NativeSourceShape` requires an explicit indexed triple or typed gap
(without itself authenticating that a declared triple is genuinely
native — that comes from the concrete ledger, executable pins, and
review). Three independent hostile reviewers plus the
public-side review returned ADMIT FOR EXTRACTION PREPARATION; the
operator then ratified the extraction selections: **promote
`Comparison/Core.lean` only; promote no native seam; keep the concrete
ledger and adapters as receipt-bound evidence custody.**

**Admission fence (binding wording):** the public calculus now contains
the closed indexed comparison framework under which the seven ratified
native-source entries were constructed and hostile-reviewed. The
concrete instantiated ledger and its native adapters remain evidence
custody, bound by the rung-5 transfer receipt and executable pin gates.
It is NOT claimed that the complete seven-entry ledger is part of the
public calculus.

**Public diff (this bundle):**

1. `LeanProofs/Admissibility/Calculus/Comparison.lean` — the
   constitutional vocabulary (closed seven-constructor `EntryIndex`,
   four dependent receipt forms, one-projection-per-entry with same-map
   receipts, receipt-bearing capabilities, typed native-source gaps,
   mandatory nonempty nonclaims, total ledgers) and 17 generic
   receipts — **normalized-source-equal** to its private source;
2. the existing Calculus aggregate imports it;
3. one `STABLE-SURFACE admissibility-calculus` custody row;
4. the fail-closed Calculus footprint gate extended 45 → 62 exact
   receipts;
5. receipts: `CLAIM-REGISTER.md` entry #23, `AGENTS.md` counts, this
   ledger. No new root, target, or top-level import; no native seam
   promoted.

**Frozen axiom footprint (rung-5 receipts):** 17 — all axiom-free. Zero
imports, Mathlib-free.

**Private realization binding (what the public code deliberately does
not carry):** the full reviewed construction is 8 modules / 60 receipts
(36 axiom-free, 15 `[propext]`, 9 `[propext, Quot.sound]`); the
public-owned Core is 1 module / 17 axiom-free receipts; the private
evidence-only remainder is 7 modules / 43 receipts — 19 axiom-free, 15
`[propext]`, 9 `[propext, Quot.sound]` — plus the fresh 16-control
hostile audit (3/6/7). `Quot.sound` is confined to that private
concrete realization. The remainder is bound by 14 definition-bound
entry-exhaustive source pins gated by
`scripts/check-rung5-source-pins.sh`, the import-free OperatorQuorum
seam gated by `scripts/check-rung5-quorum-seam.sh`, and all seven
`EntryIndex` assignments. Exact private blob pins are recorded in the
skunkworks rung-5 transfer receipt after the private reconciliation
commit; the public core does not float free of its proved inhabitant.

**Custody accounting after rung 5:** 192 public Lean sources — 95
STABLE-SURFACE, 96 PUBLIC-EVIDENCE, 1 REPOSITORY-AGGREGATE, across
eleven stable roots and 112 ownership relations (post-rung-4:
191/94/96/1, 111).

**Nonclaims:** the public promotion does not expose or prove the
concrete seven-entry ledger; no universal standing/authority/custody
carrier; no cross-family coercion; no crossing law (rung 6); no legacy
or origin-bound BreakGlass comparison (rung 7); no capital-C
completion. A future concrete public claim requires a new reviewed
selection packet.

## Rung 6 — the stored-decision crossing (admitted 2026-07-18)

**Source:** private skunkworks `Rung6Crossing/Core.lean` (blob
`31a8ccc066ea`) and `Rung6Crossing/WeatheringBoundedPaid.lean` (blob
`9ac4cddefc20`) at reconciliation commit
`e03c1b7abcea6a58c9c806f8c976dbdefab2d4a6`, built against public
baseline `ba7590af…` (candidate packet SHA-256 `04154879b2dc…`,
digest-verified). The packet's working-byte coordinates were converted
to Git pins by the reconciliation commit before extraction, per the
ratified transfer requirements.

**Review and ratification:** the preflight cycle returned REVISE on
three receipt-honesty findings (authority wording, line-vs-occurrence
counting, unfrozen pin coordinates, quoted-identifier bypasses), all
repaired in the reviewed bytes with a lexer-based decision-flow gate.
Three independent hostile reviews plus the public-side review returned
ADMIT FOR EXTRACTION PREPARATION; the public-side review independently
verified the two-`.decide` property, all four module footprints, both
gates, and the 14 public-input blobs. The operator ratified both
extraction paths and the full 28-receipt surface, including all four
fixtures and both fences — the positive result does not travel without
the vacuous-custody disclosure, the empty-obligation disclosure, the
mixed-branch/double-fault cases, and the stored-artifact controls.

**Claim fence (binding wording):** the crossing evaluates each native
family exactly once, stores the resulting judgments, and derives
verdicts, located obstructions, and exact comparison receipts solely
from that stored pair. The concrete instance establishes crossing
behavior for the declared Weathering and bounded-paid judgment shapes.
It does not establish payment, settlement, obligation transition, or
non-vacuous custody. `ExactJudgmentReceipt` observes the stored
`CheckedPacket`; it does not authorize re-evaluation of either native
family.

**Public diff (this bundle):**

1. `LeanProofs/Admissibility/Calculus/Crossing.lean` — generic core, 14
   axiom-free receipts; and
   `LeanProofs/Admissibility/Calculus/Instances/WeatheringBoundedPaidCrossing.lean`
   — concrete leaf, 14 exactly-`[propext]` receipts; both
   **normalized-source-equal** to their pinned private sources;
2. the existing Calculus aggregate imports both;
3. two `STABLE-SURFACE admissibility-calculus` custody rows, plus three
   closure-forced dual-root additions: the crossing consumes the rung-1
   substrate, so PathVerdict `Edges`, `Domains`, and `Located` join
   `Core` as intentionally dual-rooted under `path-verdict` and
   `admissibility-calculus`;
4. the fail-closed Calculus footprint gate extended 62 → 90 exact
   receipts;
5. receipts: `CLAIM-REGISTER.md` entry #24, `AGENTS.md` counts, this
   ledger. No new root, target, or top-level import.

**Frozen axiom footprint (rung-6 receipts):** 28 — 14 axiom-free
(generic), 14 exactly `[propext]` (concrete). No `Quot.sound`,
Mathlib-free. The non-overlapping accounting: the private
implementation remainder is the 3-receipt `[propext, Quot.sound]`
`LedgerEvidence.lean` tether (keeping `paidDischarge` separately
inhabited), and the 13-receipt hostile audit is counted separately.

**Custody accounting after rung 6:** 194 public Lean sources — 97
STABLE-SURFACE, 96 PUBLIC-EVIDENCE, 1 REPOSITORY-AGGREGATE, across
eleven stable roots and 117 ownership relations (post-rung-5:
192/95/96/1, 112).

**Evidence custody (deliberately NOT transferred):**
`LedgerEvidence.lean`, `Rung6CrossingAudit.lean` (13 controls incl.
arbitrary-stored-pair coherence and the retained-witness theorems), and
both legacy crossing modules (`Crossing.lean`,
`LocatedCrossingAdapter.lean`) preserved byte-for-byte as adverse
custody for the seven documented legacy defects.

**Nonclaims:** no payment/settlement/discharge law, no obligation
transition, no non-vacuous bounded-paid custody, no N-ary crossing, no
saturation-engine crossing, no witness-identity serialization, no
authenticated segment labels, no BreakGlass crossing (rung 7), no
capital-C completion.

## Rung 7 — the origin/history-bound BreakGlass terminal instance (admitted 2026-07-18)

**Source:** seven private modules at reconciliation commit
`85edee78d686e92cbf3dffb6ee3550922913c363` (candidate packet SHA-256
`e4bc2e46…`, Git blob `c5f9cdb6…`, digest-verified), built against
public baseline `721c2c8c…` (tree `935880e8…`). The packet's 27
working-byte coordinates were converted to Git pins by the
reconciliation commit before extraction.

**Review and ratification:** the internal preflight caught and repaired
a glossary overclaim (`Atoms` contains exactly origin, state, actor,
step). The public-side hostile review verified the packet digest,
reproduced the 150-receipt accounting per-module (101 stable + 49
evidence, zero `sorryAx`), independently confirmed the single stored
`evaluate` boundary and the untouched seven-entry `EntryIndex`, read the
C1 comparison in full (verdict-level, no `AuthorizedStep` fabrication,
origin-retaining audit view), and ran all three rung-7 gates plus the
233-job tree and 58-check canonical CI. The operator ratified extraction
with **explicit acceptance of the axiom footprint**: the stable surface
carries `Quot.sound` and `Classical.choice` over the declared opaque
public substrate, named per-theorem in the research-tree manifest.

**Public diff (this bundle):**

1. seven stable sources under
   `LeanProofs/Admissibility/Calculus/Instances/BreakGlass/` (lifecycle
   origin 3, native 28, lifecycle 23, governed family 19, spine 9,
   comparison 4, crossing 15 — 101 receipts), each
   **normalized-source-equal** to its pinned private source under the
   declared substitutions (including the sibling-qualifier map
   `OriginBoundBreakGlass.` → `BreakGlass.` in the crossing);
2. the Calculus aggregate imports the four leaf roots (12 imports
   total);
3. seven `STABLE-SURFACE admissibility-calculus` custody rows, plus
   seven closure-forced multi-root additions (`Authority`,
   `StateTransition`, `MeasureAccounting`, and four `Witnessed`
   sources gain `admissibility-calculus` ownership);
4. the fail-closed Calculus footprint gate extended 90 → 191 exact
   receipts, with the rung-7 expectations generated from the gate's own
   probe context;
5. the description-coherence obligation discharged: all four public
   description sites (aggregate header, lakefile, CI step, gate header)
   updated atomically to rung 7 / 191, verified by the private
   cross-repository description-coherence gate (the check lives in the
   research tree and audits the public checkout);
6. receipts: `CLAIM-REGISTER.md` entry #25, `AGENTS.md` counts, this
   ledger.

**Frozen axiom footprint (rung-7 stable receipts):** 101 —
3 axiom-free, 19 opaque-substrate-only, 4 `+propext` without
`Quot.sound`, 67 `+Quot.sound` without `Classical.choice`, and 8
`+Classical.choice` (75 `Quot.sound`-bearing overall). (The full private construction's
150-receipt split, including the 49 evidence receipts, is 3/26/13/97/11
and remains a research-tree accounting.) No `sorryAx`, no project axiom,
Mathlib-free. **This rung must never be summarized as axiom-free**; the
footprint was accepted knowingly.

**Custody accounting after rung 7:** 201 public Lean sources — 104
STABLE-SURFACE, 96 PUBLIC-EVIDENCE, 1 REPOSITORY-AGGREGATE, across
eleven stable roots and 131 ownership relations (post-rung-6:
194/97/96/1, 117).

**Evidence custody (deliberately NOT transferred):** the 39-receipt
hostile-case matrix, the 6-receipt legacy-exploit repair audit, the
3-receipt spine audit, the grouped terminal audit, the legacy
fixed-`Atoms` exploit modules (byte-pinned adverse custody), and the
blocked predecessor packet all remain in skunkworks custody.

**Nonclaims:** per claim #25 — no origin-allocator uniqueness, attestor
honesty, runtime conformance, unconditional state change, multi-entry
reordering, discharge/payment lifecycle, general transition universe, or
cryptographic claims; and rung-7 admission does not decide the terminal
campaign naming claim.

## Verification receipt (rung-7 admission tree)

All by bare exit code, 2026-07-18:

- packet digest and blob verified; 6 of 27 working-byte pins
  sample-verified; private tree — pass (233 jobs); canonical CI — 58/58;
  source pins — 19/19 (12 parity + 7 direct); decision flow — one stored
  evaluate boundary; description gate — coherent
- 150-receipt accounting independently reproduced per-module (101 + 49,
  all eleven modules exact; 3 axiom-free, 108 `Quot.sound`-bearing
  decomposing as 97 + 11 `Classical.choice`, zero `sorryAx`)
- independent greps: zero `.decide`/`.funnel`/operational
  `Rung6Crossing.check (` in the specialized modules; exactly one
  `Rung6Crossing.evaluate (`; zero `EntryIndex` references in any
  BreakGlass module
- normalized-source-equality proof for all seven transfers — EQUAL 7/7
- `bash scripts/check-calculus-footprint.sh` — pass (191/191 exact)
- `bash scripts/check-custody-classes.sh` — pass (201/104/96/1, 11
  roots, 131 ownerships)
- description-coherence gate — four sites coherent at rung 7 / 191
- full remaining battery per `AGENTS.md` — pass

## Verification receipt (rung-6 admission tree)

All by bare exit code, 2026-07-18:

- packet digest verified; private construction: full tree — pass (230
  jobs); `check-rung6-source-pins.sh` — 14/14 exact at `ba7590af…`;
  `check-rung6-decision-flow.sh` — 2/2 native decisions stored once;
  canonical audit — 54/54
- independent spot-check: exactly two `.decide` occurrences in the
  generic core, both inside `def check`; zero in the leaf; zero
  `funnel` in either proposed module
- receipt accounting independently reproduced (wrap-normalized): core
  14/14 axiom-free; leaf 14/14 `[propext]`; tether 3/3
  `[propext, Quot.sound]`; audit 12 + 1
- normalized-source-equality proof for both transfers — EQUAL 2/2
- public import-cone check — no reachable `LedgerEvidence`, audit, or
  legacy crossing module
- `bash scripts/check-calculus-footprint.sh` — pass (90/90 exact)
- `bash scripts/check-custody-classes.sh` — pass (194/97/96/1, 11
  roots, 117 ownerships)
- full remaining battery per `AGENTS.md` — pass

## Verification receipt (rung-5 admission tree)

All by bare exit code, 2026-07-18:

- private construction: full skunkworks tree build — pass (226 jobs);
  `check-rung5-source-pins.sh` — 14/14 exact, definition-bound,
  entry-exhaustive; `check-rung5-quorum-seam.sh` — exact import-free
  prefix; canonical audit — 52/52
- receipt accounting independently reproduced: 60 implementation
  receipts at 36/15/9; 16 audit receipts at 3/6/7 (wrap-normalized
  count); no `sorryAx` or `Classical.choice`
- normalized-source-equality proof for the single transfer — EQUAL
- `bash scripts/check-calculus-footprint.sh` — pass (62/62 exact; the
  17 rung-5 receipts all axiom-free)
- `bash scripts/check-custody-classes.sh` — pass (192/95/96/1, 11
  roots, 112 ownerships)
- full remaining battery per `AGENTS.md` — pass

## Verification receipt (rung-1 admission tree)

All by bare exit code, 2026-07-17:

- `lake build` (default surfaces) — pass
- `lake build PathVerdict PathVerdictEvidence` — pass, axiom receipts
  re-attested on arrival
- `bash scripts/check-pathverdict-footprint.sh` — pass (36/36 exact)
- `bash scripts/check-custody-classes.sh` — pass (181/84/96/1, 10 roots,
  100 ownerships)
- full remaining battery per `AGENTS.md` — pass

Rung 1's public commit: `538cf0b2ff2b88087fb6372ec45a6ba611a81db0`
("Admit Admissibility Calculus rung 1").

## Verification receipt (rung-2 admission tree)

All by bare exit code, 2026-07-17:

- `lake build` (default surfaces, now including `AdmissibilityCalculus`) —
  pass
- `lake build AdmissibilityCalculus` — pass, all six receipts axiom-free
  on arrival
- `bash scripts/check-calculus-footprint.sh` — pass (6/6 exact)
- `bash scripts/check-custody-classes.sh` — pass (183/86/96/1, 11 roots,
  102 ownerships)
- every other family build, footprint gate, audit script, and the pinned
  downstream consumer per `AGENTS.md` — pass (22/22 green)

Rung 2's public commit: `8b93d459683602dfb497686283f082eaa53b9f36`
("Admit Admissibility Calculus rung 2").

## Verification receipt (rung-3 admission tree)

All by bare exit code, 2026-07-17:

- private pre-transfer sanitation: full skunkworks tree rebuild — pass
  (211 jobs); unique one-owner check for every moved declaration — pass
- normalized-source-equality proof for all four transfers
  (comment-stripped diff modulo declared substitutions) — EQUAL 4/4
- `lake build AdmissibilityCalculus` — pass, all receipts re-attested on
  arrival at exactly 10 axiom-free + 6 `[propext]`
- `bash scripts/check-calculus-footprint.sh` — pass (22/22 exact)
- `bash scripts/check-custody-classes.sh` — pass (187/90/96/1, 11 roots,
  106 ownerships)
- stale-name sweep (overbroad `PaidReachability`, saturation glosses,
  custody/obligation overclaims) — clean
- every other family build, footprint gate, audit script, and the pinned
  downstream consumer per `AGENTS.md` — pass (22/22 green)

Rung 3's public commit: `f0f313107fa318637a4b58b8f014953dd988000c`
("Admit Admissibility Calculus rung 3").

## Verification receipt (rung-4 admission tree)

All by bare exit code, 2026-07-18:

- private pre-transfer sanitation: full skunkworks tree rebuild — pass
  (215 jobs); unique one-owner check for every moved declaration — pass;
  zero stale pre-rename identifiers
- normalized-source-equality proof for all four transfers
  (comment-stripped diff modulo declared substitutions) — EQUAL 4/4
- `lake build AdmissibilityCalculus` — pass, all receipts re-attested on
  arrival at exactly 18 axiom-free + 5 `[propext]` for the rung-4 set
- `bash scripts/check-calculus-footprint.sh` — pass (45/45 exact)
- `bash scripts/check-custody-classes.sh` — pass (191/94/96/1, 11 roots,
  111 ownerships incl. the intentional dual-rooted `PathVerdict/Core`)
- every other family build, footprint gate, audit script, and the pinned
  downstream consumer per `AGENTS.md` — pass (22/22 green)
