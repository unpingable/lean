# v7 Release Ledger — Artifact Authority Profiles

> **Historical record.** The Scratch paths/labels below describe the v7 tree.
> v13 rehomes the unchanged released family under
> `LeanProofs/CustodyIndexed/`, with finished fixtures in its evidence root.
> See [`V13-RELEASE-LEDGER.md`](V13-RELEASE-LEDGER.md).

**Release: v7.0.0 — Artifact Authority Profiles** (*A Lean proof release for
custody-aware authority semantics*). Umbrella: Custody-Aware Authority
Semantics. Prior release: v6.0.0 — Finite Custody Checking. Gap spec:
`docs/V7-GAP-SPEC.md` (ratified 2026-07-02; constitution binding on every
slice).

**The v7 claim (scoped, exact):** *profiles are local, crossings are paid,
receipts are not fungible across obligations, and coverage cannot be
minted.* In full:

- **Local profiles do not compose for free** — holding two profiles' local
  material is not holding their cross-profile authority
  (`profile_does_not_compose_for_free`); cross-profile conversion requires
  a declared, paid bridge receipt, and with it the crossing composes — the
  ONLY difference is the receipt (`cross_profile_conversion_requires_bridge`,
  `admission_requires_jurisdiction_receipt`).
- **Stage ascent pays each rung** — a stage-n profile does not authorize
  stage n+1 (`profile_stage_noncollapse`), and any ascent from j to k holds
  EVERY intermediate rung receipt in custody, at any derivation depth — no
  skipped rung, no bulk discount (`ascent_pays_every_rung`).
- **Receipts are scoped to obligations and are not fungible** — the generic
  evidence-jurisdiction screen (`JurisdictionFrame`/`JurisdictionRespecting`,
  minted on the two-instance family repeat, per-vocabulary and local)
  with derivational walls (`unmatched_context_cannot_convert`: nothing in
  custody scoped to the demanded obligation ⇒ underivable at any depth);
  the prior local walls are recovered as exact instances
  (`admission_jurisdiction_iff_jurisdiction_screen`,
  `stage_step_discipline_iff_jurisdiction_screen`); receipt species
  cross-use is caught (bridge-as-rung, rung-as-bridge — both satisfy the
  custody discipline and fail the screen); no receipt is scoped to every
  obligation (`UniversalReceiptFree`, total form).
- **Coverage cannot be minted** — whatever obligation a derived receipt can
  fund, its origin could already fund, at any chain length, in any
  evidence calculus over the system (`derived_evidence_covers_no_more`);
  operational funding power never exceeds declared scope
  (`operational_power_is_declared`); and in single-scoped frames covering
  k distinct obligations costs k distinct held receipts — proved as a
  lower bound AND met by an exact witness (`coverage_costs_receipts`,
  `three_obligations_cost_three_receipts` /
  `three_receipts_cover_three_obligations`). Coverage through custody is
  legitimate when paid: the theorem is *no bulk discount*, not suspicion
  of all broad custody.
- Along the way the C3 escaped animal was closed: relation-promotion
  (satisfies the discipline, evaded every screen resident at its audit) is
  caught by the minted screen (`relation_promotion_fails_jurisdiction_screen`)
  — escaped → cornered → caught.

**The v7 non-claims (binding on release notes):**
- **No shared custody language** — the no-unifier result is this campaign's
  constitution; profile field names are specimen vocabulary, never shared
  semantics. **Not a "Constellation Custody Protocol"** — that name is
  retired for releases.
- **No master profile, no universal artifact authority schema** — and the
  master screen's own limits are demonstrated in-release, not footnoted
  (`two_way_profiles_fail_master_screen`: a fully paid two-way bridge pair
  fails the index-level MasterFree screen — failing it is a smell, not a
  conviction).
- **No WLP semantics** — WLP remains envelope-only (shared syntax, never
  shared semantics) and is UNTOUCHED by v7; its non-collapse doctrine
  lines are named in the gap spec (§6), not built.
- **No runtime, no JSON schemas, no AG/NQ/Porter integration** — Lean owns
  profile laws and refusal theorems; wire formats and runtime admission
  are the AG/constellation lane.
- **No profile registry** — a registry may enumerate, never mediate; v7
  builds none at all.
- **No issuer-level / provenance-correlated portfolio accounting** — the
  named v7.x remainder: coverage acquired across acquisitions, correlated
  by issuer basis, needs a provenance model this skeleton does not have.
  Not silently solved; named.
- **No graded "too much coverage" policy screen** — deliberately rejected
  as arbitrary and false-positive-riddled; only the total god-receipt form
  is screened (`UniversalReceiptFree`).
- **Screening, not enforcement** — frames are local declarations an
  instantiator checks systems against; the screen does not force good
  jurisdiction design, and frame quality (over- or under-declaration) is
  the instantiator's visible burden.

**Custody:** all v7 modules are `Custody-Class: SCRATCH` — fenced, not
promoted kernel authority — CI-covered (build coverage ≠ promotion).
`LeanProofs.lean` imports none of them.

**Verification basis:** every module compiles clean (exit-code receipts
under `.governor/verify_receipts/`); zero `sorry`/`admit`/`native_decide`;
axiom footprints attested via `#print axioms` on every theorem (all ≤
`[propext, Quot.sound]`; slice 1 and the animal-capture and the
derivational-coverage kill are zero-axiom; no `Classical.choice` anywhere).
Adversarial audits (codex) per slice: slice 1 YELLOW→addressed in-slice
(screen scope-limit demonstrated as a theorem), slice 2 GREEN, slice 3
GREEN (emperor check passed: "screening, not enforcement"), slice 4 GREEN
("materially supports releasing v7 without a portfolio screen as
blocker"). Trail: `.governor/loop.json` +
`docs/CHANGELOG-scratch-campaign.md`.

## The modules

| Module | Load-bearing results | Axioms |
|---|---|---|
| `ArtifactProfiles` (slice 1) | two-kind specimen (observer/authority profiles, distinct evidence indices) + ONE paid bridge; **`profile_does_not_compose_for_free`**; **`cross_profile_conversion_requires_bridge`** (the paid two-cut chain); **`admission_requires_jurisdiction_receipt`** (general wall); `no_master_profile` + **`two_way_profiles_fail_master_screen`** (the screen's false positive demonstrated on an honest paid topology); FORBIDDEN parse-implies-authority specimen — satisfies the discipline, caught by local `AdmissionJurisdiction` | entirely zero-axiom |
| `ProfileStages` (slice 2) | Nat-indexed ladder, ONE rule family; **`profile_stage_noncollapse`**; **`ascent_pays_every_rung`** (Rooted induction — every rung in [j,k) literally in custody); positive pair (two stages cost two receipts); TWO cages, two mechanisms: stage-self-promotion (discipline unsatisfiability, base-only caveat recorded) and rung-skip (satisfies the discipline, caught by local `StageStepDiscipline`) | ≤ [propext, Quot.sound] |
| `JurisdictionScreen` (slices 3+4) | **`JurisdictionFrame`/`JurisdictionRespecting`** (per-vocabulary, opt-in scopes, no default fungibility); **`unmatched_context_cannot_convert`** (the keeper wall); instance IFFS recovering slices 1–2; **`relation_promotion_fails_jurisdiction_screen`** (the C3 escaped animal, caught, zero-axiom); receipt cross-use cages (bridge-as-rung / rung-as-bridge, discipline-satisfying, screen-caught); `UniversalReceipt`/`UniversalReceiptFree` (total form); **`derived_evidence_covers_no_more`** (coverage inherited, never minted — zero-axiom, via the resident anti-currency law); `operational_power_is_declared`; **`coverage_costs_receipts`** (single-scoped pigeonhole) + exact 3-for-3 price on the combined frame | ≤ [propext, Quot.sound] |

## The slogans (theorem-shaped, carried in the files)

- *Profiles are local; crossings are paid.*
- *Every rung is paid* — no skipped rung, no bulk discount.
- *A receipt funds only what it is scoped to.*
- *Coverage is inherited, never minted.*
- *No bulk discount on jurisdiction* — wealth is paid accounting, not
  forgery.
- *Failing the master screen is a smell, not a conviction* (inherited,
  demonstrated).

## Operator acts (not Claude's)

Tag `v7.0.0` (or authorize the local tag) and author the GitHub release
(release creation mints the DOI), using the claim + non-claims above as
the release-note boundary. Publish sequencing: v6.0.0 is already public;
main may be pushed with v7 at the operator's timing.
