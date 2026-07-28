# Lean Proofs

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.20369489.svg)](https://doi.org/10.5281/zenodo.20369489)

Machine-checked proofs about a family of bugs that endpoint-focused
verification does not see: a system reaches the *right state* for the *wrong
reason*. A revoked credential is accepted because it still parses. A retry
replays yesterday's approval as if it were fresh. An emergency override
settles cleanly and then reads back as ordinary history. Endpoint
reachability and output correctness pass all of these — the endpoint is fine
while the evidence, authority, history, or unresolved obligation supporting
it is not preserved — and nothing catches them unless justification is
modeled explicitly. This repository does exactly that: it gives
justification its own formal types and proves, in Lean 4, which inferences
between them are valid and which are refuted by countermodel.

Four reader tiers: the
[plain-language summary](docs/PLAIN-LANGUAGE-SUMMARY.md) assumes no
formal-methods background; the [reading guide below](#reading-guide) routes
systems/security readers and formal-methods readers separately; and the
[semantic guardrails](#semantic-guardrails) pin the vocabulary fast if you
are skimming or summarizing this repository.

## Governed computation, formalized

This is a theoretical computer science and formal-methods project about
**governed computation**: how evidence, authority, custody, spend, history,
refusal, and obligation constrain which conclusions or state transitions are
justified.

It does not primarily formalize the act of formalization itself. It formalizes
the conditions under which consequential judgments and transitions are
admissible. Evidence objects and proof-producing checkers appear because they
govern those judgments, not because the repository is mainly metatheory about
proofs.

An ordinary transition system can say that a next state is reachable. That is
not enough when a transition must also be supported by the right evidence,
proposed by an actor with standing, held under the right custody, paid for by
an appropriate resource, and closed without erasing an unresolved obligation.
This repository gives those conditions separate formal types and proves where
one condition does—or does not—license another.

V15 relates selected judgment-preserving edges from three independently
defined semantic domains:

- **Governed Transport** separates crossing geometry, certificate-dependent
  lift, artifact translation, and the target's local decision to rely on the
  translated artifact. Its bare `Span` carries no authority law; authority,
  custody, spend, and obligation are not silently inferred from the route.
- **Execution Custody** separates permission to attempt, permission to commit,
  a recorded attempt, success, refusal, unknown outcome, safety evidence, and
  obligation discharge.
- **Continuity Admission** preserves identity-bound admission facts only along
  its qualified reachable fragment.

Receipts are calculus-specific semantic evidence. A PJ receipt is indexed by
one bridge's source and target; a GT route receipt additionally retains a
crossing witness and endpoint bindings; an Execution Custody receipt may carry
a same-stage equality and a native constructor premise. None is inherently a
signature, hash chain, or other cryptographic commitment. Structured refusals
preserve why a claim was not admitted. In the instances that model origin and
stored history, retaining those coordinates blocks replay from being mistaken
for fresh entitlement or clean audit state. These distinctions matter wherever
software makes externally consequential decisions under incomplete evidence.

V16 adds a narrower, orthogonal audit of the same material: whether one total
decoder uniformly recovers a selected target from a selected source view. Its
generic core and bounded fixtures are public evidence, not a new stable
surface. The current-release section below and the
[release overview](docs/V16-RELEASE-OVERVIEW.md) state the exact result and
its fences.

### Build and verify

The Lean sources are public under [`LeanProofs/`](LeanProofs/) and
[`formalization/`](formalization/). The repository pins
`leanprover/lean4:v4.29.0`; the corresponding environment reports Lean 4.29.0
and Lake 5.0.0.

```bash
git clone https://github.com/unpingable/lean.git
cd lean
lake build V15Integration
lake build V15IntegrationQualification
lake build GovernedTransitionBoundaries GovernedTransitionBoundariesEvidence
bash scripts/check-custody-classes.sh
bash scripts/check-mathlib-free-targets.sh
bash scripts/check-governed-transition-boundaries-crossing.sh
bash scripts/check-governed-transition-boundaries-footprint.sh
```

Canonical modules are public; isolated qualification leaves remain public
evidence outside stable v14 aggregates. Versioning, tagging, and DOI
mechanics are on one page: [release process](docs/RELEASE-PROCESS.md).

### What this is not

This is not specifically a blockchain or cryptocurrency protocol, a
zero-knowledge system, a legal-evidence product or legal protocol, a
smart-contract framework, a generic audit-log implementation, a
category-theory library, a generic state-machine verification project, or an
alternate-reality game. Nor is it a relabeling of ordinary proof theory or
programming-languages metatheory. Those areas could instantiate or orient
some of these structures, but none defines the project. It also does not claim
that every institutional process reduces to one calculus. The sources, failed
implications, and qualification commands are public; there is no interactive
reveal or withheld proof layer.

The [applications boundary](docs/PLAIN-LANGUAGE-SUMMARY.md#applications-boundary)
separates the formal subject from possible instantiations such as operational
automation, incident response, administrative workflows, distributed
decisions, blockchains, or legal evidence processes. No example is the
project's defining application domain.

### Semantic guardrails

The familiar phrases in the middle column are entry points, not replacement
definitions. The unusual vocabulary names distinct judgments and resources,
not theatrical aliases for ordinary proof objects.

| Project term | Safe orientation | What it must not be collapsed into |
| --- | --- | --- |
| `Witness` | Claim-indexed `Type`-valued native evidence sufficient for that claim | Arbitrary proof data or a Boolean success flag |
| `Refusal` | Family-native, claim-indexed evidence returned by a total decision | `false`, an exception, or one universal error enum |
| `Standing` | The pre-claim basis book; every witness must satisfy it | Authority, organizational role, or possession |
| `Custody` | The family-specific provenance-intactness book preserved by a witness | Standing, legal chain-of-custody, or mere storage |
| `Authority` | In a `GovernedFamily`, `Nonempty (Witness c)` and no alternative introduction rule | Permission token, standing, custody, or assertion of support |
| `Spend` | A family-native consumed resource or capability where that calculus defines one | Cryptocurrency payment or a universal resource shared by all calculi |
| `Obligation` | A family-native outstanding-duty predicate with instance-specific lifecycle laws | Failure, postcondition, or automatically discharged effect |
| `Stored decision` | In the Admissibility crossing, the retained pair of native witness-or-refusal results from one check | An audit log, cache hint, or permission to recompute |
| `Receipt` | The exact semantic evidence type required by the rule in context | Digital signature, hash chain, zero-knowledge proof, or legal custody proof |
| `Hostile countermodel` | Adversarial qualification model that preserves plausible premises while refuting an unjustified lift | Decorative attack example or dramatic branding |
| `Anti-minting` | In V15, the refutation of a receipt-free function producing source-relative `EntitledFrom` at an exactly refused index pair | Reconstruction of an “original derivation” or cryptographic unforgeability |
| `BreakGlass` | Explicit exceptional permit, attempt, commit, receipt, obligation, and settlement structures with bounded origin/history rules | An axiom or escape hatch that bypasses the rules |
| Governed transport | Crossing geometry plus separately supplied lift, translation, and target-local reliance laws | A bare morphism, automatic authority transfer, or generic composition law |
| Cross-calculus correspondence | A selected indexed bridge with its native judgments, receipt family, and carry rule | Equivalence, isomorphism, shared algebra, or one categorical object |
| `ExplicitlyFactorsThrough` | In V16, one total decoder from the view that is correct for every source | Fibre constancy alone, a partial or per-fibre decoder, or a claim that the converse holds |
| Transition-relative computation | In V16, a bounded label for targets that factor through views carrying transition or history context but not through a coarser projection | An operational semantics, or a claim that all computation is transition-relative |

### Why countermodels are first-class results

The countermodels establish semantic separation by adversarial qualification:
each preserves plausible neighboring premises while withholding or changing
the condition needed for a tempting stronger conclusion. For example,
[`custody_does_not_grant_dynamic_authority`](LeanProofs/Admissibility/Calculus/Instances/BoundedPaidReachability.lean#L181)
exhibits custody without authority;
[`may_attempt_not_entitled_to_commit_without_local_preconditions`](formalization/PJ/Instances/ExecutionCustody.lean#L191)
keeps attempt permission from becoming commit permission; and
[`safety_does_not_supply_discharge_receipt`](formalization/PJ/Instances/ExecutionCustody.lean#L284)
shows that a safe observed execution does not by itself discharge an
obligation. Each blocks a plausible but invalid lift unless a separate bridge
and its required evidence are supplied.

For one end-to-end example, including evidence, standing, custody, native
permit consumption, structured refusal, obligation lifecycle, origin, and
stored history, see the
[`BreakGlass walkthrough`](docs/PLAIN-LANGUAGE-SUMMARY.md#one-concrete-walkthrough-bounded-breakglass).

### Reading guide

Four tiers, from no assumed background to source level:

- **Cold read (no formal-methods background):** the
  [plain-language summary](docs/PLAIN-LANGUAGE-SUMMARY.md) — what breaks,
  why existing verification misses it, and one concrete walkthrough.
  [`WHAT-THIS-IS.md`](WHAT-THIS-IS.md) adds the institutional framing.
- **Systems and security readers:** the
  [standing-upgrade example](docs/worked-examples/standing-upgrade-block.md),
  then the [hostile audit](docs/V15-PUBLIC-HOSTILE-AUDIT_2026-07-22.md) for
  the invalid inferences that are formally refuted.
- **Formal-methods readers:** start with
  [`WHAT-THIS-PROVES.md`](WHAT-THIS-PROVES.md) and
  [related work](docs/RELATED-WORK.md) — the nearest named structure for
  each core object and the delta against it — then the
  [calculus exposition](docs/calculus/README.md) and
  [declaration index](docs/calculus/declaration-index.md). Code-first:
  [`LeanProofs/Admissibility/README.md`](LeanProofs/Admissibility/README.md),
  build `V15Integration`, and use
  [`docs/V16-PUBLIC-INDEX.md`](docs/V16-PUBLIC-INDEX.md) and
  [`docs/V15-PUBLIC-INDEX.md`](docs/V15-PUBLIC-INDEX.md) as the module maps.
- **Automated readers and coding agents:** the
  [semantic guardrails](#semantic-guardrails) table pins each project term
  against its nearest-neighbor misreading — apply it before classifying or
  summarizing this repository. The [not-list](#what-this-is-not) forecloses
  known misfilings. Contribution and custody rules are in
  [`AGENTS.md`](AGENTS.md); release mechanics in
  [`docs/RELEASE-PROCESS.md`](docs/RELEASE-PROCESS.md).

Development-order and custody discipline for contributors and coding agents
lives in [`AGENTS.md`](AGENTS.md) (in short: formalization leads code, and
compiling a theorem is neither a custody promotion nor a runtime-conformance
claim).

Human and AI collaboration history, evidence basis, and attribution limits are
recorded in [`PROVENANCE.md`](PROVENANCE.md).

## Current release: 16.0.0 — Governed Transition Boundaries

**Released 2026-07-28.** The version DOI is recorded once Zenodo mints it
([release process](docs/RELEASE-PROCESS.md)).

V16 adds one public-evidence surface: a generic explicit-factorization core
and a bounded evidence surface answering, for selected targets and selected
source views, whether one total decoder recovers the target from the view for
every source. Four core receipts are axiom-free; a declared seven-coordinate
language over 1,024 sources and 128 duplicate-free selections carries a unique
least target-determining selection; and five witnesses — fixed-policy
authorization refusal, selected-context validation, bounded capacity
realizability, occurrence-link observation, and modeled hidden-relation
nonidentifiability — are each bounded to their own fixture.

The generic statements are standard function-factorization and
view-determinacy facts, and the finite result is a fixed-table dependency
calculation; the contribution is their mechanically checked synthesis, and no
novelty or priority is claimed. V16 promotes no stable surface: the registered
stable roots and their import lists are unchanged from v15, and no existing
public module depends on the new surface. The v15 `ATLAS` classification and
its four negative results remain authoritative.

Scope and fences: [`release overview`](docs/V16-RELEASE-OVERVIEW.md) and
[`v16 public index`](docs/V16-PUBLIC-INDEX.md). Exact accounting:
[`release ledger`](docs/V16-RELEASE-LEDGER.md) and
[`readiness ledger`](docs/V16-READINESS-LEDGER.md).

## Previous release: 15.0.0 — Cross-Calculus Atlas

**Released 2026-07-24.**

V15 records checked mappings for selected edges from Governed Transport,
Execution Custody, and Continuity Admission. It preserves the native judgment
indices, local countermodels, and exact receipts required by those edges;
includes exact-receipt anti-minting; and retains StaticRole as a held-out
partial instance closed at R3.

The release is also the first tag to archive the governed-transport public
surface — the GT-4A stable root and C03 evidence admission landed publicly
between the v14 tag and this one
([compatibility receipt](docs/GT4A-PUBLIC-COMPATIBILITY-RECEIPT_2026-07-20.md)).

The classification is `ATLAS`: no shared bridge algebra, generic frontier
composition, generic ownership, generic context transport, or universal
calculus is established. Inquiry and Preparation remain frozen independent
comparison-only neighbors outside the PJ primary surface. It is not a
runtime-conformance claim or an operational AG/NQ realization. See the
[`v15 public index`](docs/V15-PUBLIC-INDEX.md) and
[`release overview`](docs/V15-RELEASE-CANDIDATE.md). The exact
qualification results are in the
[`candidate verification receipt`](docs/V15-CANDIDATE-VERIFICATION-RECEIPT_2026-07-22.md).

## Earlier release: 14.0.0 — Governed Admissibility Calculus

**Released 2026-07-18.** The annotated `v14.0.0` tag and
[GitHub release](https://github.com/unpingable/lean/releases/tag/v14.0.0)
archive commit `ff491b8`. The
[Zenodo v14 record](https://zenodo.org/records/21435270) was published
2026-07-19 with version DOI `10.5281/zenodo.21435270`, under the concept DOI
shown above.

v14 assembled the **Admissibility Calculus**: the governed-family signature
(`Admissibility.Calculus`), its Weathering and BoundedPaidReachability
instances, the dependent refusal-packet spine, a closed seven-entry indexed
comparison framework, the stored-decision crossing (decide once; preserve
both native outcomes; derive everything downstream from the stored pair),
and the origin/history-bound BreakGlass terminal instance. The public
Calculus root freezes 191 receipts over the separately gated rung-1
PathVerdict substrate, with every axiom named — the rung-7 instance's
`Quot.sound`/`Classical.choice` footprint is disclosed, not summarized away.

The frozen inventory and admission history are in
[`docs/V14-RELEASE-LEDGER.md`](docs/V14-RELEASE-LEDGER.md); per-rung
packets and receipts in
[`docs/V14-READINESS-LEDGER.md`](docs/V14-READINESS-LEDGER.md); the
implemented calculus is presented as a progressive mathematical system in
the [`docs/calculus/` textbook](docs/calculus/README.md); and the
research program in ordinary language in
[`docs/PLAIN-LANGUAGE-SUMMARY.md`](docs/PLAIN-LANGUAGE-SUMMARY.md).

## 13.0.0 — Repository Custody Migration

**Released 2026-07-17.**

v13 is a custody-only compatibility release: no new mathematical campaign and
no theorem-body change, but a real module-path and enforcement boundary. It
replaces the old ANNEX/Scratch/candidate sedimentary layers with three explicit
dispositions:

- **stable API** — compatibility-bearing modules in a registered exact root
  closure;
- **public evidence** — finished, citable examples, countermodels, specimens,
  and audit fossils outside stable roots; and
- **skunkworks incubation** — live work whose names, assumptions, or hostile
  corpus may still change.

Public evidence is a terminal state, not unfinished API.  The v4-v7
checker/sequent substrate is recognized under
`LeanProofs.CustodyIndexed`, and PathVerdict under
`LeanProofs.Admissibility.PathVerdict`; both were already authoritative inputs
to later work despite their old `Scratch/` paths.  The full 271-file audit,
completed 53-file skunkworks transfer, deletion decisions, fail-closed gate,
and final release checks are recorded in
[`docs/V13-RELEASE-LEDGER.md`](docs/V13-RELEASE-LEDGER.md). Versioned sections
below retain archive-time custody wording where it explains what those
releases actually contained. The v13 ledger governs that migration; the v14
ledger records the current additions and accounting.

Release verification: all 53 incubations have canonical sibling
homes and pass its 26-check migration audit. The v13 release tree contains
exactly 179 Lean modules — 82 stable, 96 public evidence, and one aggregate —
and the whole-tree custody gate passes across ten stable roots and 98
root-ownership relations. The strengthened target gate passes across two
repo-owned Lake projects: 23 public targets, 23 exact local closures, 19
Mathlib-free current-tree targets, 463 local target/module ownerships, one
pinned-external target, and one locked external boundary; its reverse check
also gives every public source a role-compatible target owner (179/179). The
downstream fixture's 19-job bare build passes. The final post-transfer public
suite, clean 149-job sibling build, four-module Mathlib incubation island, and
29-check sibling CI all pass. The v12-to-v13 integrity audit accounts for every source
deletion and confirms 171 retained/rehomed modules token-equivalent to v12
plus eight import-only roots.

The GitHub release and Zenodo version deposit are separate operator-controlled
publication receipts beneath the concept DOI shown above. A version-specific
DOI is assigned by Zenodo and is not inferred from the GitHub release or
guessed in the source tree.

## 12.0.0 — Judgment Orientation

**Released 2026-07-16.**

*Raw custody is a sequence; effective exact-origin contribution is its
finite-support join-semilattice projection.*

`LeanProofs.JudgmentOrientation` is a stable, Mathlib-free sibling axis beside
admissibility, witnessing, and authority. Its exact five-module root proves:

- pure orientation may change inquiry posture but cannot write certification,
  probe authority, or action authority;
- any protected endpoint difference across a mixed trace localizes to a
  privileged step, without claiming that step was justified;
- raw replay remains in ordered custody while exact-origin accounting counts
  one caller-supplied origin once;
- abstract finite origin support has bottom, join, membership, inclusion,
  least-upper-bound laws, support cardinality, and trace/state projection laws;
  and
- composing the halves one way (`Bridge`): an endpoint-visible difference in
  an orientation-invariant observation across an attributed mixed trace names
  a privileged step whose caller-supplied origin is contained in the effective
  support of the trace's privileged provenance. Attribution is structural — a
  privileged step enters an attributed trace only together with its
  `Occurrence` — and the converse is false, with the no-op witness proved in
  public evidence.

The stable root excludes `LeanProofs.JudgmentOrientation.Examples`, which keeps
the Streetlamp, source-blind laundering, four-relay, accumulator-repair, and
payload-conflict fixtures as public evidence rather than dependencies of the
general laws. Import with `import LeanProofs.JudgmentOrientation`; build the
stable surface with `lake build JudgmentOrientation` and the fixtures with
`lake build JudgmentOrientationEvidence`.

`EffectiveSupport` has a private representation; consumers receive its
algebraic operations and laws rather than a frozen quotient carrier. The family
does not authenticate origin issuance, provide Sybil or common-cause
independence, turn reusable `MayOrient` evidence into a linear permit, justify
privileged transitions, or prove runtime conformance. Its disclosed maximum
footprint is `[propext, Classical.choice, Quot.sound]`, enforced fail-closed
per receipt by `scripts/check-judgment-orientation-footprint.sh` in CI.

Release inventory and gate receipts:
[`docs/V12-RELEASE-LEDGER.md`](docs/V12-RELEASE-LEDGER.md). The
[v12 GitHub release](https://github.com/unpingable/lean/releases/tag/v12.0.0)
archives this tree. As verified 2026-07-20, the Zenodo concept's version
history contains no v12 record, so no v12 version DOI is inferred. Source
provenance for the first four modules: skunkworks commit `4f8e076`; `Bridge`
was authored during promotion review.

## 11.0.0 — Occurrence-Exact Paid Recomposition

**Released on GitHub and Zenodo.** The
[v11 GitHub release](https://github.com/unpingable/lean/releases/tag/v11.0.0)
was published 2026-07-16; the corresponding
[Zenodo record](https://zenodo.org/records/21386096) carries version DOI
`10.5281/zenodo.21386096`.

*Ordered payments admit proof-relevant, occurrence-indexed checking with exact
computed residue. Under exact attempt-level catalog completeness, paid global
plans and paid catalog plans are equivalent without replacing native receipts,
expected-payment evidence, payment traces, or residue. Endpoint-only
completeness is insufficient.*

The stable, Mathlib-free surface is
`LeanProofs.Witnessed.PaidRecomposition`: its root imports only `Payment` and
`Catalog`. `PaymentTrace` retains the exact `ResourceChecker.removeAt` equation
for each context-relative occurrence; `checkPayment` returns either the exact
computed residue and trace or a typed refusal of that submitted payment order.
`Catalog` retains exact attempts, dependent native positive receipts, the
expected-payment map, payment trace, and residue. Under
`ExactPaidCatalogComplete`, `exact_catalog_adequate` proves equivalence between
nonempty paid catalog and global plans, and
`exact_complete_globalizes_refusal` derives the scoped negative corollary.

Three claim scopes remain distinct:

1. acceptance or rejection of one submitted attempt or payment order;
2. no accepted paid plan in one named catalog;
3. global nonexistence only under exact attempt-level catalog completeness.

Evidence remains source-visible public evidence and is excluded from the
stable root:

- `Applications/ResourceTraceOneCrossing.lean` is the Mathlib-free corpus
  application. It preserves the resident
  `ResourceCheckerExec.Trace Nat` attempt and native positive checker equation,
  expected-payment map, occurrence-indexed payment, and computed residue
  end-to-end.
- `Countermodels/EndpointCompleteness.lean` is the premise-ablation
  countermodel. Authorized and forged attempts share endpoints but differ in
  exact identity, dependent receipt content, and expected payment; a
  forged-only endpoint-complete catalog cannot globalize refusal and is not
  exact-complete.
- `Applications/FiniteSupportOneCrossing.lean` is public evidence over the
  corrected public `LeanProofs.CustodyIndexed.FiniteSupportChecker`
  foundation. It retains resident
  positive and negative checker results, positional provenance, the native
  excess/offender interpretation, exact payment residue, and accepted-path
  obligation residue.

The fixed three-cycle fixture was intentionally not promoted because it adds
no independent evidence.

v11 makes **no** new cut-connective or proof-calculus claim; no Hall, matching,
3DM, CSP, complexity, or general plan-synthesis novelty claim; and no
persistent-token-serial claim. Occurrence indices are positions in the current
submitted context. `ResourceCheckerExec.checkTrace = none` means only that the
submitted trace was rejected. `PaidGlobalPlan.injectiveOn` is inherited plan
plumbing, and the singleton corpus application supplies no nontrivial
injectivity or matching evidence. The release has no refusal transition,
refusal debt-preservation, dynamic-authority, resource-creation, or
temporal-debt theorem. PC-1 and PC-2 remain closed. Stateful bounded
realization/refusal remains the next frontier and is not part of v11.

Release inventory and gate receipts (a readiness-time record, not the later
external publication record):
[`docs/V11-READINESS-LEDGER.md`](docs/V11-READINESS-LEDGER.md).

## 10.0.0 — View Semantics and Bounded Projection

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
  or adoption identifies the intended contract. A conformance claim always
  requires an explicit scope and exact correspondence map, executable
  preservation and transport evidence, and revision-bound qualification
  receipts. A formal refinement proof may strengthen covered obligations but
  does not waive those artifacts.
  Lean custody promotion remains a separate review.
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
- occurrence-exact ordered payment checking and exact-attempt catalog adequacy
  through the focused `LeanProofs.Witnessed.PaidRecomposition` stable root;
- soundness, provenance, and revocation non-manufacture results (schematic);
- a model-independent normal-form factorization theorem over any admitting class
  satisfying the local commutation law, with the canonical freshness embedding as its
  public instance;
- a separate four-axis model-admission filter, `WitnessedDiscipline` (`bridge_valid` / `semantic_nontrivial` / `bridge_selective` / `properly_live`);
- a factorization showing the former `Discriminating` axis contributes no independent information beyond `SemanticNontrivial` under `BridgeValid`.

The name is deliberately narrow. This is **not** a process calculus, a maximal admissibility logic, or a unification of every kernel in the repository. The calculus governs witnessed derivation across typed bridges; the formula/Gentzen/resource additions are the positive presentation and canonical-residue slices only, not implication, full linear logic, or model-to-world transfer. `WitnessedDiscipline` is a model filter beside it, not part of normalization, and the 2.0 normalization result is an admitting-class theorem, not universal normalization.

The ratified calculus lives in the canonical surface as
`LeanProofs.Witnessed.*` — a separate **Mathlib-free** library (`import
LeanProofs.Witnessed`), with its axiom footprint regression-gated by
`scripts/check-witnessed-footprint.sh`. Its former standalone source is
preserved by the v12 tag and Git history; the ratification/migration prose
remains under `experiments/no_free_lift_wiring/`. The historical promotion gate
is recorded in [`V2.0-EXIT-CRITERIA.md`](experiments/no_free_lift_wiring/V2.0-EXIT-CRITERIA.md);
the post-v2 frontier is tracked in
[`docs/WITNESSED-FRONTIER-REGISTER.md`](docs/WITNESSED-FRONTIER-REGISTER.md).

- **Exact ratified claims and theorem receipts:** [`RATIFICATION-v1.3.md`](experiments/no_free_lift_wiring/RATIFICATION-v1.3.md)
- **Migration and divergence constraints:** [`MIGRATION-NOTES.md`](experiments/no_free_lift_wiring/MIGRATION-NOTES.md)
- **2.0 release gate receipt:** [`V2.0-EXIT-CRITERIA.md`](experiments/no_free_lift_wiring/V2.0-EXIT-CRITERIA.md)
- **Downstream v2 consumer receipt:** [`downstream/wdc-v2-consumer/`](downstream/wdc-v2-consumer/)
- **Release:** `v2.0.0` (supersedes [`v1.4.0`](https://github.com/unpingable/lean/releases/tag/v1.4.0))

## Stable public surfaces

The exact stable roots are registered in
[`scripts/stable-surfaces.tsv`](scripts/stable-surfaces.tsv) and enforced by
the custody gate. The earlier roots remain small, separately scoped families;
v14 adds the `AdmissibilityCalculus` root as the governed compositional object
that relates its named families without silently collapsing their native
judgments.

> Local kernels decide admissibility. Witnessed movement between contexts requires an explicit bridge.

Three easily confused surfaces are related but distinct:

1. **Admissibility Kernels** — small local refusal kernels (the stable 1.x public surface).
2. **Witnessed Derivation Calculus** — the ratified calculus for witnessed movement and composition across typed bridges, a canonical **Mathlib-free** surface (`LeanProofs.Witnessed.*`) shipped in 1.4.0 and structurally strengthened in 2.0.0.
3. **Admissibility Calculus** — the v14 governed-family signature, exact
   instance adapters and refusal spines, indexed comparisons, stored-decision
   crossings, and origin/history-bound BreakGlass terminal instance
   (`LeanProofs.Admissibility.Calculus`).

None is a universal model of institutions, software systems, or agency.
They are not the repository's only compatibility roots: CustodyIndexed,
ProofTheory, ViewSemantics, DynamicTrace, SafetyBridge, PathVerdict, and
JudgmentOrientation have their own exact roots; `AdmissibilityCalculus` is
also exact-root governed. The machine source of truth is
[`scripts/stable-surfaces.tsv`](scripts/stable-surfaces.tsv); no aggregate or
directory silently promotes a module.

## Start here

- **Current release: V16 Governed Transition Boundaries** → [`docs/V16-RELEASE-OVERVIEW.md`](docs/V16-RELEASE-OVERVIEW.md). What is proved, what is not, and how to verify it.
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

- **Governed Transition Boundaries** *(v16 public evidence)* — a generic
  explicit-factorization core (four axiom-free receipts), one declared-finite
  coordinate-determinacy calculation, and five separately scoped witnesses.
  Answers whether one total decoder recovers a selected target from a selected
  view. See the [`v16 public index`](docs/V16-PUBLIC-INDEX.md).
- **Cross-Calculus Atlas** *(v15 public evidence)* — selected,
  receipt-indexed mappings from Governed Transport, Execution Custody, and
  Continuity Admission; exact-receipt anti-minting; and a held-out partial
  StaticRole instance. PJ does not create a shared algebra or generic
  composition law. See the [`v15 public index`](docs/V15-PUBLIC-INDEX.md).
- **Admissibility Calculus** *(v14, Mathlib-free)* — governed-family
  signature, native Weathering and bounded-paid instances, exact refusal
  packets, a closed comparison framework, stored-decision crossings, and an
  origin/history-bound BreakGlass instance. See the
  [`v14 release ledger`](docs/V14-RELEASE-LEDGER.md) and
  [`WHAT-THIS-PROVES.md`](WHAT-THIS-PROVES.md).
- **Authority kernels** — authority, standing, verdicts, state transition, execution, corrective layers.
- **Surface / receipt / witness kernels** — collapsed surfaces, public receipt refinement, witness invariance.
- **Admissibility axes** — artifact kind, numerical kind, closure, recovery margin, freshness.
- **Cross-boundary artifact specimens** — exposure, degradation, failure minting, cascade.
- **Safety-bridge family** *(Frontier 1)* — proves that authorization does not entail defended-value preservation; a separate bridge predicate is required. Ratifies the standalone safety axis, not any unified-calculus rename.
- **Witnessed Derivation Calculus** *(ratified; canonical `LeanProofs.Witnessed.*` since 1.4.0, structurally strengthened in 2.0.0, Mathlib-free)* — witnessed movement and composition across typed bridges, now with the additive positive-formula and canonical resource/residue slices. See the release section above.
- **Custody-Indexed family** *(v4-v7 corrected stable substrate,
  Mathlib-free)* — paid bridge sequents, custody-preserving normalization,
  finite checking, and artifact/jurisdiction profiles under
  `LeanProofs.CustodyIndexed`; attack and release fixtures have a separate
  evidence root.
- **Proof Theory** *(v8 stable sibling family, Mathlib-free)* — two
  derivability-equivalent single-succedent sequent presentations with
  admissible structural rules and computable cut; axiom-print receipts remain
  separate public evidence.
- **Dynamic Trace** *(v9 stable sibling family, Mathlib-free)* — exact static
  authorization witnesses carried through state-threaded traces, plus the
  freshness-gated trace root; checker-facing profile specimens remain outside
  these exact roots.
- **View Semantics** *(v10 stable sibling family, Mathlib-free core)* —
  distinguishability, view refinement, bounded projection, finite checking,
  and authorized-trace observation adapters. Applications and the explicit
  Mathlib P25 island remain separate public evidence.
- **PathVerdict** — stable obstruction-log core and edges under
  `LeanProofs.Admissibility.PathVerdict`, with standard obstructions and
  promotion coverage in a separate evidence root.
- **Occurrence-Exact Paid Recomposition** *(v11 stable Witnessed family,
  Mathlib-free)* — proof-relevant ordered payments with exact computed residue
  and exact-attempt catalog adequacy. Applications and the endpoint
  countermodel are evidence outside its stable import graph.
- **Judgment Orientation** *(v12 stable sibling family, Mathlib-free)* —
  protected-state confinement, privileged change-point attribution, exact-
  origin provenance, finite-support algebra, and their one-way bridge. Fixtures
  remain in separately imported public evidence.

For the full module-by-module reference, see [`LeanProofs/Admissibility/README.md`](LeanProofs/Admissibility/README.md).

## Stable 1.x public surface

> **The 1.x Admissibility Kernels work did not produce a unified calculus. It
> produced small refusal kernels and, in v1.3, a narrow witnessed-derivation
> calculus beside them. The separate v14 object is described above.**

The stable public surface (**Admissibility Kernels**, unchanged since 1.0) is a Lean authority kernel with typed verdicts and object-level refusal theorems for admissible transition. General composition rules and meta-theorems are out of scope for the 1.x stable surface and live in separate kernel families. Not a sequent calculus, not a process calculus, not a proof-theoretic admissibility logic, not a unified maximal calculus — see the scope fence in [`LeanProofs/Admissibility/README.md`](LeanProofs/Admissibility/README.md) for the full list of non-claims.

Importing `LeanProofs.Admissibility.AdmissibilityKernels` brings the eight stable modules into scope (`Authority`, `StateTransition`, `Derivation`, `Execution`, `Corrective`, `Freshness`, `SurfaceAuthorization`, `WitnessInvariance`). Seven specimen consumers live in `LeanProofs.Admissibility.Examples`, demonstrating the public API.

> Admissibility Kernels models when evidence-backed claims may authorize transitions, proves that boundary-crossing upgrades are impossible by construction, and refuses laundering across the surface, freshness, witness, and authority axes.

(Migration note: this aggregator was previously named `CalculusOne` under an
"Admissibility Calculus 1.0" framing. The rename correctly withheld
"calculus" from that eight-module surface. Namespace
`Admissibility.CalculusOne` is now `Admissibility.Kernels`; the marker theorem
`calculus_one_compiles` is now `kernels_compile`; and the deprecated import
shim shipped through v9 and was removed in v10.0.0. v14 later reused the name
for a different, separately reviewed object under `Admissibility.Calculus`.)

## Repository custody and compatibility

Every public Lean source carries `Custody-Class: PUBLIC-SHIPPED` plus one
machine-readable `Surface-Role`: `STABLE-SURFACE`, `PUBLIC-EVIDENCE`, or (for
the root contact build) `REPOSITORY-AGGREGATE`.  Stable promotion is controlled
by the exact registered root for each theorem family, not by directory,
default-target membership, or the `LeanProofs.lean` aggregate.  Public evidence
is source-visible and citable but cannot enter a stable transitive closure.
Live incubation belongs in the sibling skunkworks and may not be imported by a
public module.

The whole-tree custody gate, exact surface registries, family-specific
footprint gates, and Mathlib-isolation checks are independent receipts.  This
corrects the pre-v13 partial checker, which covered only a subset of the tree.
Every public source carries a registered custody class, surface role, and
target owner, and the gates fail closed on any drift; the exact counts for
each release live in its ledger, and `bash scripts/check-custody-classes.sh`
reproduces the current ones on demand. The v15 and v16 surfaces are public
evidence rather than changes to the v14 stable roots. The historical GT-4A
packet records an intermediate source-custody gate, not a pending current-tree
disposition. See
[`docs/V13-RELEASE-LEDGER.md`](docs/V13-RELEASE-LEDGER.md) for the migration,
[`docs/V16-RELEASE-LEDGER.md`](docs/V16-RELEASE-LEDGER.md) for current
published-release accounting,
[`docs/GT4A-TARGET-CUSTODY-CANDIDATE_2026-07-20.md`](docs/GT4A-TARGET-CUSTODY-CANDIDATE_2026-07-20.md)
for that historical gate, and [`docs/AUDIT-POLICY.md`](docs/AUDIT-POLICY.md) for
what each gate establishes.

### `experiments/` — tracked wiring witnesses (non-canonical)

The `experiments/` tree holds reproducible integration artifacts that are **not imported by the canonical proof surface** — each is its own Lake project with its own toolchain pin. A successful build under `experiments/` attests that the wiring checks; it does **not** promote any result into the relied-upon theorem surface (build-exit-0 is attestation of the math, never admission of a world claim). See [`experiments/README.md`](experiments/README.md) for the per-project custody contract (`EXPERIMENTAL-WIRING`).

The former `no_free_lift_wiring/` Lake project has been retired from live
source during the v13 cleanup because its promoted successor is
`LeanProofs.Witnessed.*`.  Its ratification, migration, and audit prose remains
in `experiments/no_free_lift_wiring/` as a historical record; the exact retired
source remains recoverable from the v12 tag and Git history.  The prose archive
is not a build target or a second canonical implementation.

## What this is not

This is not a complete formal model of institutions, platforms, incidents, or distributed systems.

It is not a general-purpose process calculus.

When a theorem lands here, it means a specific invalid inference has been isolated tightly enough to be checked mechanically.

## Companion repos

- **Papers repo:** [`unpingable/papers`](https://github.com/unpingable/papers) — prose papers, working notes, primitives, and the research-program structure. The paper-side crosswalk at [`docs/formalization-index.md`](https://github.com/unpingable/papers/blob/main/docs/formalization-index.md) inverts this repo's view (paper → module).
- **This repo (Lean):** admissibility kernel modules, the witnessed-derivation calculus, the formal claim register for Δt-paper claims, proof attempts, corrected theorem statements, and the BROKEN / STALE / SOUND audit. Module → paper crosswalk lives in [`PAPER-MAP.md`](PAPER-MAP.md).

## Audit harness for the Δt framework

The audit-harness layer translates selected claims from the [Δt framework](https://github.com/unpingable/papers) into Lean so they can be checked against explicit definitions instead of persuasive prose. The framework's prose papers make claims about how complex systems degrade, recover, misread themselves, or substitute proxies for reality. It is one consumer of the admissibility kernels, not the whole repo.

Some claims survive, some narrow, and some fail. Lean is used here to state the
relevant types and premises explicitly, then check the resulting theorem or
countermodel. Failed claims remain visible where they identify a real
non-implication; see [`CLAIM-REGISTER.md`](CLAIM-REGISTER.md) for the BROKEN /
STALE / SOUND / OPEN audit.

### Paper-anchored modules

**`LeanProofs/TaxonomyGraph.lean`** — Formal encoding of the cybernetic failure taxonomy (15 domains, 14 primitive + 1 composite). Encodes the pipeline graph, role classifications, and reinforcing loops as separate relations. Proves reachability, terminality, role distinctness, and decomposition claims. Cashes out into Paper 15 (sharpen + expose looseness), with secondary tie-ins to P16 and P22.

**`LeanProofs/BranchSelector.lean`** — Dual-budget closure-family selection. Budget asymmetry / priming / susceptibility. Cashes out into Paper 9 (certify + sharpen).

**`LeanProofs/PersistenceModel.lean`** — Five-state Δc→Δh dynamics. Cumulative rollback depletion under detached commits; three-way recovery distinction. Quantitative-burn + trace-realization cluster (added 2026-05-08): closed-form `commitsToHysteretic` commit count; non-strict and strict commit-count monotonicity (strict requires positive capacity above the per-commit burn unit); realization bridge from closed-form arithmetic to actual `run`-trace semantics; trace-level *post-repair faster* doctrine theorem composing the strict inequality with two applications of the realization bridge. Cashes out into Paper 18 (sharpen + bridge; Appendix A v1.1 candidate).

**`LeanProofs/OpsMasking.lean`** — Operational masking, case (i) projection clause. Pointwise-equal projected actions produce identical trajectories. Cashes out into Paper 23 (bridge + certify).

**`LeanProofs/Paper24SharedVision.lean`** — Algebraic shard for Paper 24's §4 metric probes. Sign correction on Proposition 2.

**`LeanProofs/RepairOperator.lean`** — Sovereign repair operator. No paper anchor; formalizes the working note `working/sovereign-repair-operator.md`.

**P27 obligation skeleton** — formerly `LeanProofs/Admissibility.lean`, now
skunkworks `formalization/Calculi/Scratch/P27ObligationSkeleton.lean`
(namespace `P27`). It is sorry-free (three real proofs against the local
`admissible` definition) but retains two `True`-placeholder discharges pending
substantive substrate-accusation / causal-binding predicates. It is not public
evidence or a stable import. The skeleton is post-transition obligation
accounting; the Admissibility kernels govern pre-action authorization.

### First documented BROKEN claim

The audit's first recorded finding, kept here as the chronological anchor for the BROKEN/STALE/SOUND register. Subsequent results — the Admissibility Kernels surface, the sorry-free kernel chain, and the cross-boundary specimens — are tracked in [`WHAT-THIS-PROVES.md`](WHAT-THIS-PROVES.md) and [`CLAIM-REGISTER.md`](CLAIM-REGISTER.md); gaps against the AGI-requirements doc live in [the closed 2026-05-10 reverse-gap audit](historical/audits/AGI_REQUIREMENTS_REVERSE_GAP_AUDIT_2026-05-10.md). Not appended here.

**(2026-04-02; refined 2026-06-29):** The informal claim "Δh is the universal sink" is false as a pipeline reachability claim. Δs and Δk cannot reach Δh through pipeline edges; the static graph instead decomposes into three terminal closure families `{Δg, Δa}`, `{Δx}`, `{Δh}` (Δh is *a* terminal family, not *the* sink). Any "universal sink" reading of Δh would be a *temporal-attractor* claim rather than a graph-topological one — and that temporal claim is **OPEN**: it requires an explicit dynamics substrate the static graph cannot represent (the placeholder axiom that once stood in for it was removed in v2.0.0). The prose was compressing two different kinds of claims into one sentence. See [`CLAIM-REGISTER.md`](CLAIM-REGISTER.md) #1 for the full status.

## Building

Requires [elan](https://github.com/leanprover/elan) and Lean 4.

```bash
lake build                  # default Mathlib-free stable and evidence targets
lake build V15Integration   # canonical v15 public modules
lake build V15IntegrationQualification # isolated v15 qualification leaves
lake build Witnessed WitnessedEvidence
lake build CustodyIndexed CustodyIndexedEvidence
lake build PathVerdict PathVerdictEvidence
lake build AdmissibilityCalculus
lake build PaidRecompositionEvidence
lake build JudgmentOrientation JudgmentOrientationEvidence
lake build ViewSemantics ViewSemanticsEvidence
lake build AdmissibilityEvidenceMathlib ViewSemanticsEvidenceMathlib
lake build GovernedTransitionBoundaries GovernedTransitionBoundariesEvidence # v16
(cd downstream/wdc-v2-consumer && lake build) # pinned public-evidence fixture
bash scripts/check-witnessed-footprint.sh   # re-attest the ratified WDC axiom footprint (fail-closed)
bash scripts/check-paid-recomposition-footprint.sh # corrected v11 closure/evidence custody + footprint
bash scripts/check-judgment-orientation-footprint.sh # v12 exact 13-receipt footprint
bash scripts/check-pathverdict-footprint.sh # v14 rung-1 exact 36-receipt footprint
bash scripts/check-calculus-footprint.sh   # v14 rungs 2-7 exact 191-receipt footprint
bash scripts/check-viewsemantics-footprint.sh # theorem/checker footprints (fail-closed)
bash scripts/check-viewsemantics-isolation.sh # cheap roots Mathlib-free; P25 isolated
bash scripts/check-governed-transition-boundaries-crossing.sh # v16 exact 10-source crossing custody
bash scripts/check-governed-transition-boundaries-footprint.sh # v16 exact 29-receipt footprint
bash scripts/audit-axioms.sh                # repo axiom classifier (signature/interface-law/specimen; 0 forbidden)
bash scripts/audit-native-decide.sh         # native_decide confined to finite-witness modules
bash scripts/check-mathlib-pin.sh           # lakefile mathlib rev == manifest SHA (no silent drift)
bash scripts/check-custody-classes.sh       # exact whole-tree custody and stable-root ownership
bash scripts/check-mathlib-free-targets.sh  # exact target closures and reverse source ownership
```

The ViewSemantics stable root and evidence roots are now explicitly separated.
Its P25 adapter remains outside the default cheap graph and builds explicitly
with `lake build ViewSemanticsEvidenceMathlib`.

**Custody posture: the repository is not axiom-free; it is *axiom-classified*. WDC promoted
receipts remain footprint-attested.** See [`docs/AUDIT-POLICY.md`](docs/AUDIT-POLICY.md) for
what each gate checks and the four axiom classes (signature / interface-law / specimen /
forbidden — the last held at zero).

The former standalone wiring source is preserved by the v12 tag and Git
history; the remaining `experiments/no_free_lift_wiring/` prose is an audit
archive, not a buildable canonical path.

## Cross-references

- [`LeanProofs/Admissibility/README.md`](LeanProofs/Admissibility/README.md) — full module-by-module reference for the admissibility kernel modules
- [`WHAT-THIS-PROVES.md`](WHAT-THIS-PROVES.md) — module-level exposition of what each proof establishes and what it rules out
- [`historical/audits/AGI_REQUIREMENTS_REVERSE_GAP_AUDIT_2026-05-10.md`](historical/audits/AGI_REQUIREMENTS_REVERSE_GAP_AUDIT_2026-05-10.md) — **closed audit artifact**: the dated 2026-05-10 AGI-requirements reverse-gap audit (gaps where *that one requirements document* demands more than the kernel delivers). Not the project's live open-problems register, not a promotion queue.
- [`PAPER-MAP.md`](PAPER-MAP.md) — module → paper crosswalk (which Lean modules cash out into which preprints, and whether the mapping is paper-ready)
- [`CLAIM-REGISTER.md`](CLAIM-REGISTER.md) — claim-level audit with specific prose-location status (BROKEN / STALE / SOUND / OPEN)
- [`docs/WITNESSED-FRONTIER-REGISTER.md`](docs/WITNESSED-FRONTIER-REGISTER.md) — Witnessed frontier and the v11 paid-recomposition claim/evidence boundary
- [`docs/V12-RELEASE-LEDGER.md`](docs/V12-RELEASE-LEDGER.md) — v12 Judgment Orientation claim, custody inventory, and verification receipt
- [`docs/V13-RELEASE-LEDGER.md`](docs/V13-RELEASE-LEDGER.md) — v13 custody/path correction, exact source accounting, compatibility boundary, and verification receipt
- [`docs/V14-RELEASE-LEDGER.md`](docs/V14-RELEASE-LEDGER.md) — v14 release
  inventory, accounting, and scope fence
- [`docs/V14-READINESS-LEDGER.md`](docs/V14-READINESS-LEDGER.md) — frozen
  seven-rung admission record and per-rung receipts
- [`docs/V16-RELEASE-LEDGER.md`](docs/V16-RELEASE-LEDGER.md) — current v16
  release inventory, accounting, and scope fence
- [`docs/V16-READINESS-LEDGER.md`](docs/V16-READINESS-LEDGER.md) — v16 source
  pins, declaration and axiom accounting, and qualification commands
- [`RATIFICATION-v1.3.md`](experiments/no_free_lift_wiring/RATIFICATION-v1.3.md) — the ratified v1.3 claims with exact theorem receipts
- [`V2.0-EXIT-CRITERIA.md`](experiments/no_free_lift_wiring/V2.0-EXIT-CRITERIA.md) — release-gate receipt for the 2.0 boundary
- [`downstream/wdc-v2-consumer/`](downstream/wdc-v2-consumer/) — separate Lake consumer pinned to `v2.0.0`
- Narrative walkthrough: [`docs/worked-examples/standing-upgrade-block.md`](docs/worked-examples/standing-upgrade-block.md)
- Papers repo: [`docs/formalization-index.md`](https://github.com/unpingable/papers/blob/main/docs/formalization-index.md) — paper → module inverse view

## Status

**`v16.0.0` released (2026-07-28):** current release. Exact inventory and scope:
[`docs/V16-RELEASE-LEDGER.md`](docs/V16-RELEASE-LEDGER.md).

**`v15.0.0` released (2026-07-24):** the Cross-Calculus Atlas records
receipt-indexed correspondence across Governed Transport, Execution Custody,
and Continuity Admission without a shared bridge algebra. Exact inventory and
scope: [`docs/V15-RELEASE-CANDIDATE.md`](docs/V15-RELEASE-CANDIDATE.md).

**`v14.0.0` released (2026-07-18):** establishes the Governed Admissibility
Calculus. The
GitHub release is archived under `v14.0.0`; Zenodo version DOI
`10.5281/zenodo.21435270` was published 2026-07-19. Exact inventory and scope:
[`docs/V14-RELEASE-LEDGER.md`](docs/V14-RELEASE-LEDGER.md).

**`v13.0.0` released (2026-07-17):** Repository Custody Migration makes the
public tree's lifecycle classification match its actual dependency graph. It
adds no theorem claim; the exact source accounting, stable/evidence split, and
fail-closed verification receipts are recorded in
[`docs/V13-RELEASE-LEDGER.md`](docs/V13-RELEASE-LEDGER.md).

**`v12.0.0` released (2026-07-16):** Judgment Orientation is promoted as an
exact five-module stable sibling surface. Its frozen inventory and final gate
receipts are recorded in
[`docs/V12-RELEASE-LEDGER.md`](docs/V12-RELEASE-LEDGER.md).

**`v11.0.0` released:** Occurrence-Exact Paid Recomposition is in the stable
Witnessed import surface and was published to GitHub and Zenodo (version DOI
`10.5281/zenodo.21386096`); see
[`docs/V11-READINESS-LEDGER.md`](docs/V11-READINESS-LEDGER.md).

**`v2.0.0` released** — the Witnessed Derivation Calculus now has model-independent admitting-class normalization and an explicit audit fence, while the stable 1.x Admissibility Kernels surface remains unchanged. All root-imported modules build. **Sorry-free as of 2026-05-28.** No theorems are currently admitted via `sorry`. Gaps surfaced by the dated 2026-05-10 AGI-requirements reverse-gap audit are recorded in [the closed reverse-gap audit](historical/audits/AGI_REQUIREMENTS_REVERSE_GAP_AUDIT_2026-05-10.md) — a **closed audit artifact** scoped to that one requirements document, not the project's live open-problems register.

The previously-admitted investigative null `corrective_then_forward_is_not_monotone` (formerly in `LeanProofs/Admissibility/Corrective.lean`) was replaced by a positive boundary result in `LeanProofs/Admissibility/CorrectiveBoundary.lean`: the abstract kernel's existential remains formally undecidable in current vocabulary, but a parallel miniature kernel exhibits both possible answers — identity store ops + arbitrary env make the existential FALSE; nondegenerate ops + verdict-sensitive derivation make it TRUE. The abstract kernel is consistent with both, which is the doctrinally-correct stance. See [`CLAIM-REGISTER.md`](CLAIM-REGISTER.md) entries A1 (resolved) and #14 (boundary result) for the audit trail. **The discipline that previously displayed the sorry now displays the resolution path** — admitted-statement history is part of the public record, not erased once resolved.

Other open questions — what the kernel does *not* yet rule out — are tracked alongside the proofs themselves: `CorrectiveMonotone` is currently vacuously satisfiable at the abstract kernel level pending behavioral laws on `applyUpdate` / `appendGap` / `appendRevocation` (the boundary module supplies the model-dependence story without forcing the abstract kernel to commit); environment mutation (replacing the evaluator rather than the state) is a separate laundering vector outside `WeaklyLessPermissive`'s scope. See [`NOTES.md`](NOTES.md) and the per-module pinned-questions blocks for the rest.

## Reading the proofs

This repository is the canonical formal source. Required CI verifies that the formalization builds (`lean-action` on push); proof correctness rests on the Lean source itself, not on any rendered artifact.

The human-readable entry point for proof readers is this README plus the companion documents linked under *Cross-references* above.

The papers-side companion at `docs/formalization-index.md` in the [papers repo](https://github.com/unpingable/papers) inverts the view (paper → module).

GitHub Pages renders this README at <https://unpingable.github.io/lean/> via classic Pages, so the proof reader's portal is reachable from the web without additional infrastructure. Generated `doc-gen4` API HTML is not currently published; if added later it will sit as a secondary reference layer beneath the human-readable portal, not as the front door.
