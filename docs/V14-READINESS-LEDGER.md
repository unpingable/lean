# v14 Readiness Ledger — Governed Admissibility Calculus

**Status: in-flight campaign ledger. Nothing here is released, tagged, or
minted.** Baseline: `v13.0.0`
(`54ffd53fa61d179b8b15f9195e877e1fefcfbd27`, 2026-07-17), the
custody-reconciliation release that made the repository capable of receiving
this campaign. The v13 tag is an immutable external baseline; this campaign
performs no tag action.

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
| 1 | `Domains`/`Located` as shared public substrate in the `path-verdict` root | **ADMITTED 2026-07-17** (this ledger, below) |
| 2 | `GovernedFamily` signature and generic laws | pending |
| 3 | Weathering and DPCR instances | pending |
| 4 | Exact refusal-packet spine (`SpineEncoding`/`LosslessEncoding`) | pending |
| 5 | Indexed comparison ledger | pending |
| 6 | Global crossing and executable checker | pending |
| 7 | Origin/history-bound BreakGlass instance (terminal forcing instance) | pending |

All seven rungs belong to one v14 semantic release unless rungs 4–6 expose a
semantic redesign large enough that the public surface cannot honestly
stabilize in this cycle (the recorded split rule).

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

## Verification receipt (rung-1 admission tree)

All by bare exit code, 2026-07-17:

- `lake build` (default surfaces) — pass
- `lake build PathVerdict PathVerdictEvidence` — pass, axiom receipts
  re-attested on arrival
- `bash scripts/check-pathverdict-footprint.sh` — pass (36/36 exact)
- `bash scripts/check-custody-classes.sh` — pass (181/84/96/1, 10 roots,
  100 ownerships)
- full remaining battery per `AGENTS.md` — pass
