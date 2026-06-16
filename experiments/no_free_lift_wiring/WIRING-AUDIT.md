# Wiring Audit — the full Admissibility-Calculus composition (playground)

**Status:** Observed — the whole constructed stack compiles together under the
canonical toolchain. **Not** observed: the stack is canonical, the embedding is
faithful, the doctrine line is ratified, or the word "calculus" is allowed back
indoors. This note keeps the breaker box open: every circuit labeled, every new
trust named.

**Build:** `cd playground/wired && lake build` → **exit 0, 11 jobs**, toolchain
`leanprover/lean4:v4.29.0` (matches canonical `~/git/lean`), Mathlib-free.

---

## 1. Import DAG (acyclic; schema upstream, model downstream)

```
CarryLaws ──┬── Coordinates ──┐
            └── Divergence ───┼── Freshness ──┐
Authority ───────────────────┘                │
NoFreeLift ─────────────────────────────────── Embedding ── CoCompilation ── Wired(root)
```

- **Upstream / schema** (import no model code): `CarryLaws`, `NoFreeLift`,
  `Coordinates` (`Coordinates` imports only `CarryLaws`).
- **Midstream / modeled kernels**: `Divergence`, `Authority`, `Freshness`.
- **Downstream / modeled embedding**: `Embedding`, `CoCompilation`.

Directionality is the load-bearing fact for §8: nothing downstream flows back up.

## 2. Formerly-standalone results, now reachable in one build

| Scratch lab file | Wired module | brought in |
| ---------------- | ------------ | ---------- |
| MinimalTransportSignature | `CarryLaws` + `Coordinates` | transitivity coordinate, interval transport |
| DivergenceTransport | `CarryLaws` + `Divergence` | triangle coordinate, widening meter |
| FreshnessTransport (was FreshnessCalculus) | `Freshness` | double-entry calculus, load-bearing, decay |
| UnifiedAdmissibilityBreaks (Authority part) | `Authority` | verdict kernel (no-bridge) |
| NoFreeAdmissibilityLift | `NoFreeLift` | the spine |
| — (new) | `Embedding` | the wire: Authority ⊕ Freshness into the spine |

## 3. Build result

`lake build` exit 0 (the exit code is the gate, not eyeballed). Per-module
isolation available via `lake env lean Wired/X.lean`.

## 4. Axiom footprint — every headliner, in the wired build

| Theorem | Module | Axioms |
| ------- | ------ | ------ |
| `transitivity_is_the_cost_of_sound_carry_forward` | CarryLaws | **none** |
| `triangle_is_the_cost_of_divergence_transport` | CarryLaws | **none** |
| `transport_sound_under_transitive_relation` | Coordinates | **none** |
| `no_free_lift` | NoFreeLift | **none** |
| `no_bridge_no_lift` | NoFreeLift | **none** |
| `lift_is_local_or_paid` | NoFreeLift | **none** |
| `paid_lift_sound` | NoFreeLift | **none** |
| `naked_lift_unsound` | NoFreeLift | **none** |
| `freshness_transport_sound` | Freshness | **none** |
| `transport_adds_power` | Freshness | **none** |
| `freshness_decays` | Freshness | **none** |
| `freshness_bridge_valid` | Embedding | propext, Quot.sound |
| `embedded_lift_sound` | Embedding | propext, Quot.sound |
| `authority_is_conservative` | Embedding | propext |
| `freshness_lift_has_freshness_origin` | Embedding | propext |

`propext`/`Quot.sound` are standard Lean core (from Sum/structure/`decide`/rw
machinery), not `sorryAx`. Disclosed, not hidden.

## 5. Per-theorem custody class

- **abstract-coordinate** (axiom-free, no model): both `CarryLaws` lemmas,
  `Coordinates.transport_sound_under_transitive_relation`.
- **schema** (axiom-free, abstract over `Claim`/`Kernel`/`Bridge`): all five
  `NoFreeLift` theorems.
- **modeled-embedding** (a model is fixed; `propext`/`Quot.sound`): everything in
  `Freshness`, `Divergence`, `Authority`, and all `Embedding` theorems.
- **doctrine/posture**: none promoted. "Admissibility Calculus is legal for this
  object" remains a sentence in prose, not a theorem.

## 6. New trust introduced BY wiring

Exactly one new modeled trust: `Embedding` fixes a concrete `Claim := AuthClaim ⊕
FreshClaim` over `(Nat, <, fun a b => b - a)` and supplies `Sem`/`Bridge`
instances. Everything else was already standalone-checked; wiring only added the
instantiation. No schema or coordinate result gained a dependency.

## 7. ModelBound residue (what still needs a fidelity review)

- `FreshAt` is a MODEL of canonical `Fresh` (no skew term, coherence dropped,
  divergence abstracted to `dist`). Exact for the model; faithfulness open.
- `Embedding`'s `Sem`/`Bridge` are one chosen instantiation; that they model the
  real authority/freshness kernels is unverified.
- The naming sentence ("calculus is legal for this object") is posture, not
  ratified.

## 8. Laundering-seam check — CLOSED

> Did wiring create any theorem described as schema-level that secretly depends
> on a modeled embedding?

**No.** Two independent proofs:

1. **DAG direction** — `CarryLaws`, `NoFreeLift`, `Coordinates` import no model
   module (verified: their `import` lines reference only `CarryLaws` or nothing).
   A theorem cannot depend on a module it does not transitively import.
2. **Axiom footprint** — every schema/coordinate headliner reports *"does not
   depend on any axioms"* **in the wired build** (§4). If wiring had laundered a
   modeled embedding into a schema theorem, that theorem would carry the model's
   `propext`/`Quot.sound`. None do.

Import reachability is electrical continuity; custody is the DAG direction plus
the axiom footprint. Both confirm the schema layer stayed clean.

---

## Adversarial review (codex, gpt-5.5) — verdict and response

Codex read the wired sources and returned (verbatim verdicts):

1. **The wire** `freshness_bridge_valid` discharges `BridgeValid` — **REAL**
   (calls `freshness_transport_sound` with the bridge's receipt + exact budget;
   not circular).
2. **`freshness_lift_has_freshness_origin`** (no cross-axis laundering) —
   **OVERCLAIM**: true, but mostly because `Bridge` is definitionally `False`
   across summands; the theorem propagates that design choice.
3. **`Claim := ⊕` faithful embedding** — **OVERCLAIM**: a tagged disjoint union
   with one active bridge family, not an interaction-preserving composition of
   two independent calculi.
4. **`Kernel := Sem` makes `embedded_lift_sound` meaningful** — **VACUOUS**:
   kernel soundness becomes identity, so it proves only bridge-preservation of
   `Sem`, not independent local-kernel admissibility.
5. **`paid_lift_sound` trivialized** — **OVERCLAIM** (schema theorem real
   generally; this instantiation removed the local burden).
6. **Subsidy** — **STRAWMAN** (no authority bridge, no cross bridge; airtight).

> Codex's one-sentence verdict: *"this earns a sound paid-transport result for
> the freshness bridge inside a tagged union, but calling it 'a sound
> admissibility calculus of paid transport between kernels' is a definitional
> dodge."*

**Response (what changed, what stands):**

- **Fixed (finding 4/5, a real bug):** `Embedding` no longer sets `Kernel := Sem`.
  It is parameterized over an abstract floor `K` with a genuine
  `EnvSound K : ∀ c, K c → Sem c` obligation. `embedded_lift_sound`,
  `authority_is_conservative`, `freshness_lift_has_freshness_origin` are now
  over abstract `K` — the local-kernel burden is real, not identity. Rebuilt green.
- **Relabeled (finding 2/3, framing honesty):** the `no_cross` theorem's docstring
  now states it is true BY DESIGN (Bridge `False` across summands) and that the
  substantive content is the JUSTIFICATION for that design —
  `naked_lift_unsound` + `bridged_unsound` — i.e. the office *enforces* the
  no-cross decision rather than *discovering* it. "Composition of two kernels" is
  downgraded to "two kernels side by side, one with a paid transport family."
- **Accepted as-is:** codex's overall verdict. This composition is **not** "the
  Admissibility Calculus." It is: the promoted spine, instantiated with a real,
  sound, paid freshness-transport bridge family and a bridge-inert authority
  kernel, with cross-axis lift structurally absent and that absence justified by
  the unsoundness theorems. Honest scope, ModelBound.

---

## Reconciliation vs canonical `~/git/lean` (read-only)

| Wired (playground) | Canonical `Admissibility.*` | Relation |
| ------------------ | --------------------------- | -------- |
| `Wired.NoFreeLift` (Lift, PaidFrom, no_free_lift, …, naked_lift_unsound) | `Admissibility.NoFreeLift` | **statement-identical** (canonical notes "proofs unchanged"); namespace differs |
| `Wired.CarryLaws.transitivity_is_the_cost_of_sound_carry_forward` | `Admissibility.CarryLaws.carry_forward_iff_transitive` | same statement, canonical renamed (legitimation prose stripped) |
| `Wired.CarryLaws.triangle_is_the_cost_of_divergence_transport` | `Admissibility.CarryLaws.budgeted_carry_iff_triangle` | same statement, renamed |
| `Wired.Authority` | `Admissibility.Authority` | study copy; NOT the canonical kernel |
| `Wired.Freshness`, `Wired.Embedding` | — | no canonical counterpart; new modeled layers |

Toolchain aligned (4.29.0). Canonical is Mathlib-based and namespaced
`Admissibility.*`; the wired tree is Mathlib-free and `Wired.*`. The spine and
coordinates the wired composition stands on are exactly the ones already promoted
canonically; the `Embedding`/`Freshness` layers are playground-only and ModelBound.

## Hardening round (steps 1–3 + items B, D) — built and re-reviewed

Build: 14 jobs, `lake build` exit 0. Per-theorem axioms re-audited (schema layer
unchanged, still axiom-free). New modules: `CanonicalFreshness`,
`CanonicalEmbedding`, `Families`.

**Step 1 — canonical adapter (`CanonicalFreshness`).** Reconstructs the FULL
canonical `Fresh` (coherence + skew + symmetric `absSub`). `canon_fresh_transports`
carries all three conjuncts (coherence free, window by transitivity, ball by
triangle); `canon_fresh_to_freshAt` is the adapter, dropping ONLY the coherence
conjunct and disclosing it (`_hcoh`). **Codex: REAL** (forward-transport scoped).

**Step 2 — second bridge family (budget-weakening).** Sound and syntactically
distinct, but **codex: semantically just ball-monotonicity** — a modest second
family, relabeled as such, not a new interaction.

**Step 3 — authority↔freshness cross edge (`Embedding.cross_edge_dichotomy`).**
First framing ("unpayable") was a codex-flagged overclaim. Corrected to the
honest dichotomy: the cross edge is UNSOUND if unpaid (`cross_axis_unpaid_unsound`,
`cross_bridge_cannot_be_valid`) and REDUNDANT if valid (`valid_cross_bridge_is_redundant`
— a valid cross edge only lands on already-true freshness). No edge is both sound
AND reach-adding. This is `no_sound_calculus_adds_power` localized to the edge.

**Item B — real canonical embedding (`CanonicalEmbedding`).** `Kernel` over
canonical `CanonFresh`, `Bridge` = reviewed canonical transport,
`embedded_canon_sound` via `paid_lift_sound` discharged by the reviewed
`canon_bridge_valid`. **Codex: ALL REAL** — on full canonical `Fresh`, the
`EnvSound K` obligation is genuine (the earlier `Kernel := Sem` vacuity is fixed),
the soundness is meaningful. This is the embedding that answers "the model is
stripped": the floor IS the canonical predicate.

**Item D — multi-family non-subsidy (`Families`).** Six families, family-local
`Bridge`; the four named non-subsidy theorems
(`freshness_bridge_cannot_pay_standing`, `standing_bridge_cannot_pay_freshness`,
`authority_cannot_buy_transport`, `transport_cannot_mint_authority`) plus the
general `bridge_is_family_local`. **Codex: overclaim if oversold** — these are
true BY the family-local `Bridge` definition (API guardrails / structural
plumbing), NOT discovered semantic separation; and the non-freshness families are
typed, inhabited STUBS (no per-family `Sem`/`BridgeValid`). Recorded as such.
Honest scoping of the non-subsidy:

| pair | status |
| ---- | ------ |
| authority ↔ freshness (`authority_cannot_buy_transport`, `transport_cannot_mint_authority`) | structural AND semantically backed by `Embedding.cross_edge_dichotomy` |
| freshness ↔ standing, and all other cross pairs | structural ONLY (no `Sem` for standing/custody/contraction/consumer-fresh yet) |

So non-subsidy is proven structurally for all six families; it is *semantically
justified* (a cross edge would be unsound) only for the authority↔freshness pair
so far. The rest is scaffolding awaiting per-family semantics.

## Rolling loop — Standing graduated (1 of 4 stubs)

`Wired/Standing.lean` runs ChatGPT's 8-step / chatty's 6-step loop on ONE stub
(receiver-relative adoption), all theorems axiom-free, codex-reviewed:

| step | result | codex |
| ---- | ------ | ----- |
| 1 real `Sem` | `Standing adopts j` (receiver-indexed) | real |
| 2 naked unsound | `cross_consumer_adoption_unsound` | real |
| 3 coordinate | `adoption_carry_is_delegation_closure` | **strawman** — `Iff.rfl` restates the def; content is really step 2 (trimmed in docstring) |
| 4 receipt test | bare-flag launders vs typed-receipt binds receiver | real |
| 5 canonical adapter | `canon_standing_to_standing` | real |
| 6 embedding | `stand_bridge_valid` + `stand_embedded_sound` | bridge real; soundness is a **within-consumer wrapper** (no cross-consumer lift) — relabeled |
| 7 non-subsidy | within-consumer sound, cross-consumer unsound | real |

Codex verdict: *"a real but very small receiver-indexed family, not just a stub;
the pipeline rhetoric was partly dressed-up."* Trimmed accordingly. So Standing
moves from stub → small real family; the authority↔freshness pair and now the
within-Standing cross-consumer edge are both semantically backed.

### Real-family table (all four stubs graduated; codex-ranked)

| family | status | codex verdict |
| ------ | ------ | ------------- |
| authority | real (no-bridge kernel; bridge-inert) | — |
| freshness | real — canonical embedding (full `CanonFresh`) | all real |
| consumer-freshness | real — **genuine coordinate** (clock-ordering, `Nat.le_trans`) + non-identity `alignBridge` + `frame_split` | "adds the most; least stub-like" |
| contraction | real (modest) — non-identity `SpendBridge`, conservation (`spend_never_increases`) | "modest but real"; vacuous named coordinate removed |
| standing | real (small) — receiver-indexed, unsoundness witness, receipt test | "small real family"; coordinate is a restatement (labeled) |
| custody | real (modest) — **authorized handoff** (holder transfers, gated on `auth`, `HandoffCarry` load-bearing), non-manufacture via spine | first pass was "dressed-up stub" (identity bridge); **fixed** to a real transfer |

All six families' headline theorems are **axiom-free**. Codex caught and I fixed:
Custody's identity-like bridge (now a real holder-changing authorized handoff) and
Contraction's vacuous `spend_is_monotone` coordinate (removed). The loop ran on all
four; honest content varies — consumer-freshness genuine, contraction/custody/standing
modest. None oversold past codex's verdict.

### Remaining risk (chatty's list, unresolved by compilation)

1. Is `CanonFresh` actually the canonical predicate to stand behind? (model-choice review)
2. Do custody / contraction / consumer-freshness get real `Sem`, or stay stubs?
3. Could a future cross-family edge smuggle policy through a structural guardrail?
4. Does the NAME get ratified by a human, not by the chandelier compiling?

None of these are closed by the build. The customs office compiles; ratification
is elsewhere.

### Name-early candidate (non-binding; NOT promoted)

The one durable rule this playground produced, filed per name-early/ratify-lazily:

> **A Lean theorem is evidence into the admission gate, never a receipt that
> bypasses it. `lake build` exit 0 attests the math, not any world claim.**

Scope of this entry: a candidate handle, recorded in scratch. Its promotion into
actual AG *runtime* doctrine is a custody-class / reliance-governing decision —
that step is the operator's, not the build's. (Self-application: a Lean stack
must not mint the receipt that governs Lean stacks. The candidate is evidence
into that decision, not the decision.)

## Bottom line

The full stack wires and builds together (Observed, 14 jobs, exit 0). The breaker
box held: no schema theorem laundered by import-continuity. Codex ran three
adversarial passes and earned its keep each time: it caught the `Kernel := Sem`
vacuity (fixed — `CanonicalEmbedding` now carries a real floor obligation), the
"unpayable" overclaim (corrected to the sound-or-redundant dichotomy), and the
budget-weakening / family-stub overclaims (relabeled as monotonicity and
scaffolding). What stands, honestly: the promoted spine; the abstract coordinates;
a real embedding on the FULL canonical `Fresh`; and six-family family-local
plumbing with structural non-subsidy (semantically backed only authority↔freshness
so far). Not a roof over the kernels, not yet canonical, ModelBound where stated —
a customs office, now wired to a real canonical kernel and scaffolded for more.

## Rename log (semantic cleanup, no theorem content)

2026-06-16 — de-placarded two misleading module names (tree compiles unchanged, no proof changed):
- `Contraction.lean` -> `BudgetMonotonicity.lean` (proved property is metric budget-monotone, NOT structural contraction; no no-replay/linearity in Lean).
- `Composition.lean` -> `CoCompilation.lean` (proves only co-compilation `True`, NOT a composition result; the real composition theorem is the open ticket in `COMPOSITION-CLASSIFICATION-TARGET.md`).
Reason: fresh readers were inferring properties supplied by filenames. Strip the placards before stating the theorem.
