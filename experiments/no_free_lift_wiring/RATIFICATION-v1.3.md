# Ratification Record — Witnessed Derivation Calculus (v1.3 candidate)
Status: RATIFIED
Ratified by: operator
Artifact commit: 5eb5629
Date: 2026-06-17

Verdict:
- Claim 1 accepted with stated scope.
- Claim 2 accepted with stated BridgeValid qualification.
- Claim 3 accepted with stated calculus/discipline separation.
- All listed non-claims remain in force.

**Surface:** `experiments/no_free_lift_wiring/Successor/` (Custody-Class: EXPERIMENTAL-WIRING; NOT in `defaultTargets`).
**Public 1.2 surface (`LeanProofs/Admissibility/`): untouched.** This is the v1.3 *candidate* experiment surface — **not a 2.0 release**.
**Name:** **Witnessed Derivation Calculus** (narrow). "Admissibility Calculus" is **not** revived (retired 2026-06-03).

Three claims, each limited to exactly what the compiled theorems establish. Every receipt below
is `#print axioms`-checked. Correspondence legend: `proved internally` · `implemented instance` ·
`convergent evidence` · `future candidate`.

---

## Claim 1 — The witnessed-derivation calculus is earned `[proved internally]`

*As the project's candidate-name criterion* (judgment + composition + cut + soundness + provenance
+ non-manufacture + normalization) — **not** an abstract universal claim and **not** a public unifier.

`Lift K B c` is a **defined inductive judgment** (`Wired.NoFreeLift.Lift`: origin + one paid bridge
step), not a theorem. The package proved over it:

| Property | Receipt | Axioms | Scope |
|---|---|---|---|
| composition along a paid path | `WitnessedDerivation.derivation_extends_along_paid_path` | none | schematic |
| genuine multi-context cut | `Tightened.cut_admissible_general` | none | schematic |
| soundness | `NoFreeLift.paid_lift_sound` | none | schematic |
| provenance | `NoFreeLift.no_free_lift` | none | schematic |
| non-manufacture | `WitnessedDerivation.revoked_floor_derives_nothing` | none | schematic |
| normalization (canonical form) | `Normalization.bridge_path_normal_form` | `[propext]` | **freshness `Embedding.Bridge` model** |
| ↳ hinge (no new law needed) | `Normalization.perm_weaken_carry` | none | freshness model |
| ↳ two-edge corollary | `Normalization.bridge_path_two_edge_normal_form` | `[propext, Quot.sound]` | freshness model |

**Scope fence (load-bearing):** composition, cut, soundness, provenance, and non-manufacture are
schematic over any kernel/bridge. **Normalization is established for the freshness `Embedding.Bridge`
model, not for every possible witnessed-derivation instance.** v1.3 earns the name by exhibiting the
*full package in a canonical model*, not by proving an abstract universal normalization theorem.

Three further fences, so the framing cannot outrun the theorems:

- **No general normalization is claimed.** The total order on freshness *time* is load-bearing —
  it is what makes a canonical form tractable. Authority and standing carry no such order; there is
  no normalization theorem for them, and none is asserted.
- **Soundness is relative, and its burden is named.** `BridgeValid Sem B` *is* the assumption that
  every single bridge step preserves `Sem` (`∀ c c', Sem c → B c c' → Sem c'`). `paid_lift_sound`
  derives soundness of the *transitive closure* from that single-step burden by induction — it
  does not assume its conclusion. This is a legitimate relative theorem, not circular plumbing.
- **Non-manufacture is one direction only.** `revoked_floor_derives_nothing` covers manufacture
  (empty floor ⇒ no derivation). **Non-suppression** — an input revocation remaining represented —
  is **not built**, and may require provenance / no-drop / richer operational semantics rather than
  an ordinary derivability theorem.
- **Cut is admissibility, not elimination.** `cut_admissible_general` shows the composition a cut
  would license is already derivable in the two-rule (`base`/`cross`) closure; there is no primitive
  cut rule being normalized away. The claim is cut-*admissibility*, not cut-*elimination*.

---

## Claim 2 — Under `BridgeValid`, `Discriminating` contributes no independent information beyond `SemanticNontrivial` `[proved internally]`

| Statement | Receipt | Axioms |
|---|---|---|
| under `BridgeValid`, `Discriminating Sem B ↔ ∃ c c', Sem c ∧ ¬ Sem c'` | `DisciplineObstruction.discriminating_is_just_nonconstant_sem` | none |
| under `BridgeValid`, `Discriminating Sem B ↔ SemanticNontrivial Sem` (the factorization) | `DisciplineObstruction.bridgeValid_discriminating_iff_semanticNontrivial` | `[propext]` |
| the round-1 singleton-context cut was the `PaidFrom` specialization (secondary) | `DisciplineObstruction.cut_is_redundant` | none |

This is an **equivalence / factorization**, not a claim that `Discriminating` is false or
meaningless in isolation. The obstruction exposed its real name: under the always-present
`bridge_valid`, the axis was `SemanticNontrivial` in a relational-sounding costume. It is therefore
**retired from the canonical structure** and re-expressed as the `semantic_nontrivial` axis;
`Discriminating` is preserved in the obstruction annex as the discovered formulation.

---

## Claim 3 — Bridge selectivity is a genuine `B`-dependent axis; the discipline is factored to four `[proved internally]`

The model-admission discipline `Tightened.WitnessedDiscipline` is a **structure with four orthogonal
fields**: `bridge_valid`, `semantic_nontrivial`, `bridge_selective`, `properly_live`.

| Statement | Receipt | Axioms |
|---|---|---|
| selectivity depends on `B` (NOT Sem-determined) | `Tightened.selective_depends_on_B` | none |
| selectivity ⟂ ProperlyLive (no redundant axis) | `Tightened.selective_not_implies_properlyLive`, `…properlyLive_not_implies_selective` | none |
| excludes the universal and the dead bridge | `Tightened.trivial_universal_not_selective`, `…dead_bridge_not_selective` | none |
| excludes trivial semantics (via `semantic_nontrivial`) | `Tightened.trivial_rt_closure_excluded` | none |
| the canonical freshness embedding satisfies all four axes | `Tightened.embedding_is_witnessed` | `[propext, Quot.sound]` |
| the discipline composes with soundness/provenance | `Tightened.tightened_metatheory` | none |
| the four axes are independent — for each, a finite model where exactly it fails | `AxisIndependence.{bridge_valid,semantic_nontrivial,bridge_selective,properly_live}_independent` | none |

**Fence (load-bearing):** `WitnessedDiscipline` is a **model-admission filter beside the calculus**.
`Normalization` never imports it; adopting bridge selectivity **does not enlarge the calculus**.
The discipline's admitted class is non-empty, witnessed by the **canonical freshness embedding model**.

**Independence fence:** the four separating witnesses prove the axes are **independent /
irredundant under the present definitions** — no axis follows from the other three. This is **not**
a claim of minimality, uniqueness, or completeness: it does **not** establish that no alternative
basis (e.g. a three-axis encoding) expresses the same discipline, that these four axes are uniquely
natural, or that the taxonomy is complete for every notion of witnessed discipline.

---

## Explicitly NOT claimed

- **AG (agent_gov) correspondences** — Authority conjunction, no-free-lift parentage, non-subsidy
  origin fence, budget monotonicity, custody non-manufacture, witness-invariance: `[implemented
  instance / convergent evidence]` in AG's operational code. **Not a verified reduction, extraction,
  or proof of the Lean implementation, and NOT part of this ratification basis.** AG's operational
  receipts motivate scope and downstream relevance only. Proof→world fence preserved: a compiled
  theorem is **evidence into** an operational gate, never the receipt or authority that gate emits.
- **Refusal legibility / continuation-bearing refusal** (the AG-on-AG slice-1↔slice-2 result):
  `[future candidate]`. A sound refusal does not necessarily imply a receiver-legible or
  continuation-adequate refusal. **No theorem in the Successor package proves this; v1.3 does not
  claim it.** Named as an external frontier only.
- **Universal normalization** — see Claim 1 scope fence (freshness model, not all instances).
- **2.0 / public-surface promotion** — not claimed; 1.2 public surface untouched.

## Operator gates still open

Commit · ratify these three claims · version docs → v1.3 · push/tag · the 2.0 public-claim decision.
