# No-Free-Lift Candidate: Toward an Admissibility Calculus

**Status: FROZEN observed state — `playground/wired`, scratch/playground tier.**
Not canonical · not runtime · not a ratified name. Frozen for ratification
review: hygiene/inventory/audit edits only; no new bridge or theorem families.

- Build at freeze: `lake build` → **exit 0, 18 jobs**, toolchain `v4.29.0`
  (matches canonical `~/git/lean`), Mathlib-free.
- Size: **15 modules, ~86 theorems.**
- Companion: `WIRING-AUDIT.md` (per-theorem custody classes, laundering-seam check).

---

## 1. Claim

> A **no-free-lift** layer can host admissibility kernels and permit nonlocal
> movement of a judgment only through **typed, paid bridge coordinates**.

Mechanized: `NoFreeLift.no_free_lift` (every lift decomposes into a kernel-floor
claim plus a chain of paid bridges), `paid_lift_sound` (paid lifts are sound when
the floor is sound and bridges are valid), `naked_lift_unsound` (a receipt-free
lift can admit falsehood, hence no sound system may contain it).

## 2. Non-claim

- Does **not** collapse the kernels into one semantic domain (the 1.0
  "maximal calculus" ghost — proved empty-or-unsound upstream).
- Does **not** admit runtime claims: the artifact has **no operational verb**
  (no `main`/IO/`#eval`/`@[extern]`/`lean_exe` — pure `lean_lib` of `Prop`s).
- Does **not** make Lean proofs into operational receipts (see §10 fence).
- Does **not** assert any embedding faithfully models a real-world kernel
  (ModelBound; see §9).

## 3. Module DAG (acyclic; schema upstream, model downstream)

```
CarryLaws ─┬─ Coordinates ─┐
           └─ Divergence ──┼─ Freshness ─┬─ CanonicalFreshness ─ CanonicalEmbedding
Authority ─────────────────┘             │
NoFreeLift ──────────────────────────────┴─ Embedding ─ Families ─ {Standing,Custody,
                                                  BudgetMonotonicity,ConsumerFreshness} ─ CoCompilation
```
Schema (`CarryLaws`, `NoFreeLift`, `Coordinates`) import no model code — the
breaker-box invariant behind §5.

## 4. Theorem inventory (headliners)

- **Spine** (`NoFreeLift`): `no_free_lift`, `no_bridge_no_lift`,
  `lift_is_local_or_paid`, `paid_lift_sound`, `naked_lift_unsound`.
- **Coordinates** (`CarryLaws`): `transitivity_is_the_cost_of_sound_carry_forward`,
  `triangle_is_the_cost_of_divergence_transport`; (`Coordinates`)
  `transport_sound_under_transitive_relation`.
- **Freshness**: `freshness_transport_sound`, `both_laws_suffice`,
  `triangle_is_load_bearing`, `transitivity_is_load_bearing`, `freshness_decays`.
- **Canonical freshness + embedding**: `canon_fresh_transports`,
  `canon_fresh_to_freshAt`, `canon_bridge_valid`, `embedded_canon_sound`.
- **Authority↔freshness edge**: `cross_edge_dichotomy`
  (`cross_axis_unpaid_unsound` + `valid_cross_bridge_is_redundant`).
- **Non-subsidy** (`Families`): `{authority_cannot_buy_transport,
  transport_cannot_mint_authority, freshness_bridge_cannot_pay_standing,
  standing_bridge_cannot_pay_freshness}`, `bridge_is_family_local`.
- **Graduated families**: `Standing.*`, `Custody.*` (authorized handoff +
  `custody_originates_from_grant`), `BudgetMonotonicity.*` (`spend_never_increases`),
  `ConsumerFreshness.*` (`frame_split`, `fresh_transfers_under_clock_order`).

## 5. Axiom footprint (re-verified in the wired build)

| layer | axioms |
| ----- | ------ |
| `CarryLaws` (both costs), `Coordinates`, all five `NoFreeLift` theorems | **none** (not even `propext`) |
| `Freshness` headliners, `ConsumerFreshness` coordinate, `Custody`/`BudgetMonotonicity`/`Standing` cores | **none** |
| `CanonicalEmbedding`, `Embedding.freshness_bridge_valid` (`Quot.sound` via Sum/decide) | `propext`, `Quot.sound` |
| `Embedding.cross_edge_dichotomy`, family non-subsidy | `propext` |

**Laundering-seam check (passed):** schema headliners are axiom-free *inside the
full wired build*. Had import-continuity laundered a modeled embedding into a
schema theorem, that theorem would carry the model's `propext`/`Quot.sound`. None
do. Custody separation held; AG independently confirmed.

## 6. Family grading (codex-adjudicated; all axiom-free)

| family | grade | note |
| ------ | ----- | ---- |
| authority | real | no-bridge kernel; bridge-inert |
| freshness | real | canonical embedding on full `CanonFresh` |
| consumer-freshness | **real (most content)** | genuine coordinate (clock-ordering via `Nat.le_trans`) + non-identity bridge + frame split |
| contraction | real (modest) | non-identity spend bridge + conservation; vacuous named coordinate removed |
| custody | real (modest) | authorized handoff (holder transfers, gated on `auth`); first pass was a dressed-up identity bridge — **fixed** |
| standing | real (small) | receiver-indexed; "coordinate" is a definitional restatement (labeled) |

## 7. Codex / AG catch log (adversarial passes; what was caught and done)

1. `Kernel := Sem` made `embedded_lift_sound` **vacuous** → fixed with a genuine
   `EnvSound K` floor obligation.
2. "tagged union = interaction-preserving composition" overclaim → relabeled.
3. authority↔freshness edge "unpayable" overclaim → corrected to the
   **sound-or-redundant dichotomy** (`cross_edge_dichotomy`).
4. budget-weakening sold as a new family → relabeled as ball-monotonicity.
5. `Families` non-subsidy as "discovered separation" → relabeled as
   true-by-construction API guardrails; non-freshness families flagged stubs.
6. Standing coordinate `Iff.rfl` **strawman** → relabeled (content is the
   counterexample); "full promotion" → scoped to within-consumer.
7. Custody bridge was **identity** (forbade the handoff it modeled) → fixed to a
   real authorized handoff using `HandoffCarry`; Contraction's vacuous
   `spend_is_monotone` → removed.
8. AG independent witness: build exit 0, axiom footprint matches disclosure,
   laundering seam held; answered "can this bypass receipt discipline?" → **no
   operational actuator**; named the proof→world fence (§10).

## 8. What is canonical already (`~/git/lean`)

- `Admissibility.NoFreeLift` — **statement-identical** to the wired spine
  (canonical notes "proofs unchanged"; renamed out of `Playground`).
- `Admissibility.CarryLaws` — same two cost laws, renamed
  `carry_forward_iff_transitive` / `budgeted_carry_iff_triangle`.
- `Admissibility.Authority` — exists canonically (the wired `Authority` is a
  study copy, NOT this).

So the spine the candidate stands on is **statement-identical to canonical
modules** — but those modules (`Admissibility.NoFreeLift` / `CarryLaws`) are
themselves `UNRATIFIED-CANDIDATE`, **unwired**, committed candidate annexes
(`94df70e`, this session), *not* promoted/vetted 1.0 surface. The spine is
canonical-tracked, not canonical-ratified. Only the modeled layers below are new.

## 9. What remains playground-only (ModelBound)

`Coordinates`, `Divergence`, `Freshness`, `CanonicalFreshness`,
`CanonicalEmbedding`, `Embedding`, `Families`, `Standing`, `Custody`,
`BudgetMonotonicity`, `ConsumerFreshness`, `CoCompilation`. Open fidelity questions:
- Is `CanonFresh` the canonical predicate to stand behind? (coherence + skew +
  symmetric `absSub` modeled; real `Time` is opaque in the kernel.)
- Do the stub-grade families warrant their modeled `Sem`, or stay scaffolding?
- Non-subsidy is *semantically* backed only for authority↔freshness; the rest is
  structural plumbing.

## 10. What would count as ratification

Not "do I have a calculus?" but the explicit, narrow decisions:

1. **Name (do NOT decide under fatigue).** Ratify "Admissibility Calculus" to
   mean *the no-free-lift accounting layer over admissibility kernels*, AND
   explicitly reject *one maximal calculus collapsing the kernels*? If no:
   publish as "No-Free-Lift: Bridge-Cost Coordinates for Admissibility Kernels."
2. **Model-fidelity review** of `CanonFresh` vs the canonical kernel `Fresh`.
3. **The fence as doctrine** (mandatory before any runtime touch):

   > **A Lean theorem is evidence into the admission gate, never a receipt that
   > bypasses it. `lake build` exit 0 attests the math, not any world claim.**

   Self-application: a Lean stack must not mint the receipt that governs Lean
   stacks. This packet is *evidence into* the ratification decision, not the
   decision.
4. **AG runtime refusal tests** (next system, not this artifact): proof-as-receipt
   → refuse; missing bridge receipt → refuse; missing model-fidelity receipt →
   quarantine; naked carry → refuse; valid bridge → admit *scoped*, not global;
   wrong-family receipt → refuse.

---

## Appendix — one-screen explainer (for a smart non-specialist)

```
Kernels decide local admissibility — "is this claim OK, right here?"
Bridges move a claim across a boundary — to a later time, another consumer, a new holder.
Every bridge must pay a typed cost (a receipt): the structure that makes the move sound.
No bridge, no lift: a claim cannot travel for free, and "it travelled for free" is provably unsound.
Lean proves the ACCOUNTING SHAPE — that paid moves preserve validity and unpaid ones don't.
It does NOT decide any real case: there is no runtime here, only the bookkeeping rules.
A passing build means the math checks; it is evidence for a decision, never the decision.
```

Physics-prof gloss: it's a conservation-law argument for license/validity.
Validity doesn't teleport; to carry it across a coordinate you pay exactly the
structure that coordinate requires — transitivity for time intervals, a triangle
inequality for a drift budget, a delegation relation for receivers. The theorem
is that the books balance, not that any particular ledger entry is true.
