# NQ Judgment Model — Frozen Scratch Snapshot

**Status: SCRATCH / NON-BINDING / SNAPSHOT.** A finite Lean specimen of NQ's
testimony/admissibility/authority split. **Migrated 2026-06-18** into canonical
`~/git/lean/LeanProofs/Scratch/` from the playground `wired` workspace (frozen commit
`d26311e`, tag `playground-nqjudgments-freeze-d26311e`).

This models NQ's judgment **shape at the NQ state inspected on 2026-06-18** — it is a
**dated snapshot, not a live claim about current NQ behavior**, and it will **not** be
updated as NQ evolves. It is **not** NQ's types, **not** imported into anything in NQ,
**not** imported by `LeanProofs.lean`, **not** rc / kernel / public surface, and it
**discharges no NQ runtime behavior**. Sorry-free. **Every no-free-lift theorem is
fully axiom-free** (the ∃-countermodels and the universal laws); only the three
verdict-classifier *fidelity* lemmas carry `propext` (from `simp` reducing the
`if`-chain) — verified by `#print axioms`.

Build (canonical): `lake build LeanProofs.Scratch.NQJudgments` (or the whole default
target — it is globbed into the `LeanProofs` lib but not the public root import).
Files: `LeanProofs/Scratch/NQJudgments.lean` + `NQJudgments/{Basic,NoFreeLift,Standing}.lean`.

> **Provenance is FROZEN.** The `Source` column in the theorem table below and the
> Provenance section cite NQ files/lines **as they stood at the inspected NQ state
> (2026-06-18)**. They are a dated record of where each modeled behavior was read
> from — **not live obligations and not kept in sync**. Do not treat a drifted
> line-number as a defect in this specimen.

---

## The model in one breath

A `Claim` is nine Bool flags spanning the layers NQ actually keeps distinct. Three
judgments stack; authority is reachable only through an external operator directive,
and a refused ancestor severs the chain unless an explicit operator declaration
bridges it.

```
CanTestify           := coverage ∧ fresh ∧ ¬contradiction
AncestorStanding     := ¬refusedAncestor ∨ operatorAdmission        -- the bridge
AdmissibleWithScope  := CanTestify ∧ scopeDeclared ∧ AncestorStanding
MayBind (authority)  := AdmissibleWithScope ∧ operatorDirective     -- NQ cannot mint this
StandingAutoComplete := greenCheck ∧ alreadyPromised                -- mechanize existing promise
MayAddPublicPromise  := operatorDirective                           -- create/expand a promise
```

---

## Theorem → NQ behavior map

| Theorem | NQ behavior modeled | Source (from the read) |
|---|---|---|
| `testimony_not_authority` | can_testify does not grant binding/spending authority | `SPENDABILITY_TESTIMONY_GAP.md:38,42` "testimony is never treated as allocation authority"; `VERDICTS.md:81` "authority belongs to a separate layer" |
| `admissibility_not_authority` | admissible_with_scope ⊬ may_bind — **NQ may NOT mint spendability** | `SPENDABILITY_TESTIMONY_GAP.md:51,55` "NQ may testify … may NOT mint spendability"; "an observation … is evidence; it is not authorization" |
| `binding_requires_external_directive` / `no_self_authorization` | a finding may not become the witness that authorized itself (sixth-keeper / `SelfAuditRefusal`) | `disk_state_witness_projection.rs:83-85` (`Finding ⊬ Witness(Finding)`); `wire.rs:344-346` `SelfAuditRefusal`; `preflight.rs:929-931` |
| `refused_ancestor_blocks_binding` | ancestor loss propagates down; suppressed findings do not feed the verdict | `TESTIMONY_DEPENDENCY_GAP.md:118,181`; `publish.rs:983-1007` `MASKING_RULES`; `nq-db/preflight.rs:174-184` |
| `explicit_bridge_can_rebind` | an operator declaration can supersede ancestor loss (re-admission) | `declaration_overlay.rs:146` `declaration_supersedes_ancestor_loss`; migration `043_admissibility_declaration.sql` |
| `missing_bridge_refuses_not_fabricates` | `MissingBridge ⟹ Refusal`, not a fabricated witness ("refuses rather than fakes") | `disk_state_witness_projection.rs:14-18,103-117`; mapping doc `:139-141` |
| `verdict` + `contradiction_yields_contradictory` / `refused_ancestor_yields_cannot_testify` / `no_coverage_yields_insufficient` | the 8-verdict register; more-specific trigger wins | `preflight.rs:270-281`; `nq-db/preflight.rs:348-413` |
| `refusal_is_not_failure` | `insufficient_coverage` (failed to speak) ≠ `cannot_testify` (refused to speak) | `VERDICTS.md:71` "Failure → insufficient; refusal → cannot"; `:62` "constitutional output, not error" |
| `green_check_not_new_promise` / `green_on_admissible_still_not_new_promise` | **a green check does not authorize a new PUBLIC PROMISE** (the promise-creation slice; the inadmissible-*dispatch* slice is motivating doctrine but is NOT proved here — see Standing.lean scope note) | `loop-protocol.md:36-38`; `CLAIM_CUSTODY.md:55-59,136,184` "Replay success is not fresh authorization" |
| `green_completes_already_promised` / `standing_auto_requires_already_promised` | Lane A standing-auto: mechanize an ALREADY-PROMISED contract under standing | `loop-protocol.md:103-108`; receipt `2026-06-18T1906Z…json:5,14` "No new guarantee" |
| `adding_a_promise_requires_directive` / `standing_auto_without_directive_adds_no_promise` / `distinction_holds` | operator-directed contract strengthening: creating/expanding a public promise needs the operator naming the shape; "naming ≠ authorizing" | receipt `2026-06-18T1837Z…json:5,17`; `loop.json:35`; `loop-protocol.md:76-77,87-89` |

### The standing-auto vs operator-directed distinction (the Rosetta stone)

Two NQ receipts, same SQL-contract surface, same test file, classified apart:
- **standing-auto** (`…column-stability`): mechanizes a promise already on paper →
  authorized by class membership, no fresh operator approval → `StandingAutoComplete`
  needs `alreadyPromised`, and `standing_auto_without_directive_adds_no_promise` shows
  it mints no new promise.
- **operator-directed** (`…column-ordering`): "ADDS a promise to the public SQL
  contract … outside standing-auto" → authorized by the operator naming the shape →
  `MayAddPublicPromise` requires `operatorDirective`; `green_*_not_new_promise` shows
  a green check never supplies it.

---

## What this model does NOT prove (the fence)

1. **It does not discharge NQ runtime behavior.** The Rust evaluator, the masking
   rules, the migration triggers, the wire schema — none are verified here. This is a
   finite oracle of the *judgment shape*, not a proof about NQ's code.
2. **The flags are not NQ's types.** Nine Bools stand in for collector coverage tags,
   `AdmissibilityExport.state`, `RefusalKind`, `verdict_scope`, the loop's standing
   predicate, etc. The abstraction is lossy by design; it captures implication
   structure, not data.
3. **`MayBind` / `MayAddPublicPromise` are not NQ-side objects.** NQ has no
   `may_bind`/`may_spend` type — that absence is the point. The model represents the
   *separate authority layer* (Governor) that NQ defers to; it does not assert NQ
   contains it.
4. **No claim about export = weakening.** The model deliberately avoids proof-theoretic
   "weakening." NQ's export is *projection/forgetting* (`forget(w) ⊬ w`), not
   structural weakening; conflating them would be the theorem-name laundering NQ
   prosecutes (`WITNESSED_DERIVATION_CALCULUS_NQ_MAPPING.md:92-100`). This model does
   not touch the projection lane at all.
5. **No completeness/soundness claim for NQ's real verdict map.** `verdict` here is a
   5-way illustrative classifier with a plausible precedence; it is not NQ's full
   8-variant `compute_verdict` and proves nothing about NQ's actual triggers beyond
   the three mapping lemmas stated.
6. **The bridge is modeled, not adjudicated.** `operatorAdmission` /
   `operatorDirective` are opaque external inputs. The model proves they are
   *required*; it says nothing about when an operator *should* grant them.
7. **Not authorization for anything.** Not a ClaimKind, not a schema, not an
   evaluator, not a doctrine promotion, not an edit to NQ. Per `SPENDABILITY_…:3` and
   the loop's "naming ≠ authorizing," this note is a handle for review only.
8. **Ancestry / refusal PROPAGATION is assumed, not proved.** `refusedAncestor` is an
   opaque INPUT bit — the already-computed output of NQ's masking/ancestry logic,
   flattened from a dependency DAG to a single Bool. The model proves what the
   authority gate does *given* a propagated refusal (block unless explicitly bridged);
   it does **not** model or verify the propagation itself. (Contrast the sibling
   `ReachableDrift`, which proves propagation by induction over traces — this specimen
   sits one layer up and takes the propagated verdict as input.)
9. **External directives co-located as `Claim` fields is a finite-model convenience,
   not a custody claim.** `operatorDirective` / `operatorAdmission` are coordinates of
   the same record as the testimony flags only so the model stays a finite, decidable
   type. Their co-location does **not** assert NQ owns, computes, or contains them; the
   held-out-ness of authority is carried entirely by the theorems
   (`no_self_authorization`, `binding_requires_external_directive`,
   `admissibility_not_authority`), never by the type layout. A deeper model would
   factor them into a separate external-directive object — and would scope the
   directive as a receipt (see non-claim note at `MayBind`: `operatorDirective` is a
   single-bit under-model of `Scratch.AuthorityScope.Receipt`).

---

## Provenance

Built 2026-06-18 in playground from a read of NQ docs/tests/loop doctrine (two
Explore passes + direct reading of `WITNESSED_DERIVATION_CALCULUS_NQ_MAPPING.md`,
`SPENDABILITY_TESTIMONY_GAP.md`, `preflight.rs`) — **all as they stood at that NQ
state; these references are frozen provenance, not live obligations.** It is a sibling
specimen to the `ReachableDrift` / `AuthorityScope` Scratch tracks (same no-free-lift
discipline, NQ's register).

Frozen at playground `d26311e` (tag `playground-nqjudgments-freeze-d26311e`) and
migrated into canonical `~/git/lean/LeanProofs/Scratch/` on 2026-06-18 with the narrow
documentation repairs applied (non-claims 8–9 added; the green-check row scoped to
promise-creation; `operatorDirective` marked an under-model of `AuthorityScope`;
provenance marked frozen). Proofs are unchanged from the frozen snapshot — re-verified
green and axiom-checked under canonical. Scratch only; no rc promotion; does not
discharge NQ runtime.
