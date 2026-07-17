# v5 Release Ledger — Custody-Preserving Normalization

> **Historical record.** The Scratch paths/labels below describe the v5 tree.
> v13 rehomes the unchanged released substrate under
> `LeanProofs/CustodyIndexed/`. See
> [`V13-RELEASE-LEDGER.md`](V13-RELEASE-LEDGER.md).

**Release: v5.0.0 — Custody-Preserving Normalization** (*A Lean proof release
for custody-aware authority semantics*). Umbrella: Custody-Aware Authority
Semantics. Prior release: v4.0.0 — Custody-Indexed Sequents.

**The v5 claim (scoped, exact):** a liberal structural derivation can be
normalized into the custody discipline **iff** its reads can be paid by
occurrences — per-label occurrence counting decides normalization exactly;
otherwise normalization returns a **typed forgery refusal** whose named
offender label is itself a genuine excess-demand witness. Successful
normalization preserves the custody chain (labels and order) and conserves
occurrences for every measure, and the positional occurrence trace proves
**who paid**: each read funded by a distinct original-context occurrence, no
occurrence paying twice, nothing paying that was not there.

**The inversion (the v5 thesis):** classical normalization removes detours
and preserves derivability. Custody-preserving normalization removes only
policy-licensed detours and **refuses** when removal would erase payment. The
same liberal syntax, priced by two disciplines, gets two verdicts: Cartesian
derives, linear refuses. *Normalization cannot forge payment.*

**The v5 non-claims (binding on release notes):**
- **Not full Gentzen cut elimination** — under the v4 discipline there are no
  cut redexes (the F7 already-normal theorem); v5 normalization eliminates
  *structural* detours (weakening/contraction/exchange) and prices reads.
- **Not a full structural-rule algebra** — Cartesian structural nodes
  (slice 1) + read-payment linearization (slices 2–4); node-form *linear*
  structural rules are named follow-up.
- **Not runtime** — proof discipline only; enforcement is the NQ/AG lane.
- Scoped to the liberal/linear normalization skeleton over the v4 sequent
  systems; the `linearizeT` ↔ `linearize` coherence theorem (traced twin vs
  untraced normalizer, label projection) is **named, not built** (v6 lane) —
  the release claim says "traced twin", not "same object".
- The decision boundary is semantic (`∀ l`); the executable finite-support
  checker is the v6 checker lane.

**Custody:** all v5 modules are `Custody-Class: SCRATCH` — fenced, not
promoted kernel authority — CI-covered under the `CustodyIndexedSequents`
build target (build coverage ≠ promotion). `LeanProofs.lean` imports none of
them.

**Verification basis:** every module compiles clean (exit-code receipts under
`.governor/verify_receipts/`); zero `sorry`/`admit`/`native_decide`; axiom
footprints re-attested via `#print axioms` (all ≤ `[propext, Quot.sound]`;
the slice-1 structural layer and the F7 seed are **zero-axiom**; a
`Classical.choice` intrusion in slice 2 was caught and purged). Adversarial
audits (codex) per slice; slice-3 verdict **count-level GREEN**; slice-4
verdict **v5.0.0 TAGGABLE** under the scoping above. Trail:
`.governor/loop.json` + `docs/CHANGELOG-scratch-campaign.md`.

## The modules (all post-v4 scratch)

| Module | Load-bearing results | Axioms |
|---|---|---|
| `DerivationData` (F7 seed) | `Deriv` reification; `eentail_iff_nonempty_deriv` reflection; `chainOf` as data; **`all_derivs_read_rooted`** — the already-normal theorem: under the v4 discipline there are NO redexes; normalization is the identity until structural rules enter as priced nodes | zero-axiom |
| `StructuralNormalization` (slice 1) | `SDeriv` = explicit `wk`/`ctr`/`exch` detour NODES over the Cartesian layer; `normalize` (structural recursion, terminating by construction); **`chainOf_normalize`** — the custody spine survives as list equality; `normalize_read_rooted` — normalization lands back in the discipline class | zero-axiom core |
| `LinearNormalization` (slices 2+3) | `linearize` — computable PARTIAL normalizer paying each read with a distinct first-match occurrence (`removeFirstC` proof-carrying); **`linearize_ok_conserves`** (occurrence conservation, every measure); `chainOf_linearize`; **`excess_demand_forges`** (accounting-tied refusal, offending trees statable); the concrete pair (pay-twice funds / free contraction forges, kernel-evaluated); `occurrences_not_labels`; `cartesian_statable_but_linearly_refused`; **`linearize_ok_iff_counts_suffice`** — THE DECISION THEOREM (counting decides normalization, one iff); `counts_suffice_for_linearize` (first-match order-safe, by-label); **`forgery_offender_is_excess`** (the offender is a witness, not a symptom); `linearize_forges_iff_excess` | ≤ [propext, Quot.sound] |
| `OccurrenceTrace` (slice 4) | `linearizeT` — traced twin recording WHICH occurrence paid WHICH read (deterministic by construction, no choice); **`linearizeT_ok_conserves`** / `trace_determines_consumed_multiset` (the trace IS the consumed multiset); `trace_labels_are_reads` (trace refines the read spine, in order); **`linearize_trace_occurrences_distinct`** (no occurrence pays twice); `trace_mem_initial` + count form (nothing pays that was not there); `same_label_distinct_occurrences_traced` (kernel-evaluated: equal labels, distinct recorded payments) | ≤ [propext, Quot.sound] |

## The slogans (theorem-shaped, carried in the files)

- *The rule relation is the sole authority map* (v4, inherited).
- *A fork may duplicate information, but not spendability* — here:
  Cartesian freedom does not license linear contraction.
- *Labels explain what was read; occurrence traces prove who paid.*
- *Normalization cannot forge payment.*

## Operator acts (not Claude's)

Tag `v5.0.0`, author the GitHub release (release creation mints the DOI),
using the claim + non-claims above as the release-note boundary.
