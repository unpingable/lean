# v4 Release Ledger — Custody-Indexed Sequents

> **Historical record.** The Scratch paths/labels below describe the v4 tree.
> v13 rehomes the unchanged released substrate under
> `LeanProofs/CustodyIndexed/`. See
> [`V13-RELEASE-LEDGER.md`](V13-RELEASE-LEDGER.md).

**Release: v4.0.0 — Custody-Indexed Sequents** (*A Lean proof release for
custody-aware authority semantics*). Umbrella: Custody-Aware Authority
Semantics. Prior release: v3.0.0 — Bounded Lifecycle Calculi. Named next
target: v5 — Custody-Preserving Normalization.

**The v4 claim:** a parameterized indexed-sequent skeleton exists in Lean in
which structural read discipline is explicit, bridge composition preserves
provenance, index connectivity does not imply derivability, master shapes are
screened on both faces (universal indices and universal evidence), and derived
evidence cannot become universal bridge currency — every cross-index
derivation roots in read evidence whose original scope funded it.

**The v4 non-claims:** no master `Admissible`; no default bridge transitivity;
no runtime enforcement; read discipline only (no full split/merge/exchange
structural algebra — named follow-up); **no cut elimination** (v5's target;
the read-rooted normal form is the shape v5 must preserve).

**Custody:** all campaign modules are `Custody-Class: SCRATCH` — fenced, not
promoted kernel authority — and CI-covered as the `CustodyIndexedSequents`
build target (build coverage ≠ promotion; the v3 lesson, applied).
`LeanProofs.lean` imports none of them.

**Verification basis:** every module compiles clean (exit-code receipts under
`.governor/verify_receipts/`); zero `sorry`/`admit`/`native_decide`; axiom
footprints re-attested via `#print axioms` (all ≤ `[propext, Quot.sound]`;
the load-bearing walls and both normal-form theorems are **zero-axiom**).
Adversarial audits (codex) per slice; final slice verdict **GREEN — v4
earned**. Trail: `.governor/loop.json` + `docs/CHANGELOG-scratch-campaign.md`.

## The ladder (S0–S4, post-v3 scratch)

| Module | Load-bearing results | Axioms |
|---|---|---|
| `BridgeSequent` (S0+S1) | indexed bridge cut sound against real `ProjectionAuthorized`; `no_free_cross_cut` (syntactic, all contexts/targets/depths); `pAuth_derivation_roots_in_assumptions` | zero-axiom syntactic layer; soundness propext |
| `ExecutionSequent` (S2) | conservation of authority (`trajectory_accounting`, generic measure); no-double-spend walls; Δt wall (fresh-at-commit minimal pair) | ≤ [propext, Quot.sound] |
| `ExecutionObligationSequent` (S3) | three linear books; receipt-linearity wall (`one_receipt_cannot_license_two_discharges`); exact `discharge_inversion`; `no_silent_discharge` | ≤ [propext, Quot.sound]; inversions zero-axiom |
| `BridgeCompositionSequent` (S4) | `composition_cannot_erase_bridge_evidence` (bounded normal form, scope stated); `mint_without_downstream_axioms_requires_all_three`; `no_free_transitivity`; `first_bridge_alone_does_not_compose` | zero-axiom syntactic layer |

## The generalization (the v4 object proper)

| Module | Load-bearing results | Axioms |
|---|---|---|
| `CustodyIndexedSequent` | generic `System`/`Entail`; ONE discipline (`EvidenceNeverConcluded`) → `evidence_only_by_assumption`, `no_evidence_synthesis`, **`entail_iff_rooted`** (normal form, arbitrary depth), `composition_preserves_provenance` (first-class chains), `closed_index_invariant` (needs no discipline); `MasterFree`/`UniversalCrossroads` + `s4_master_free` (screen, both failure modes named in-file); diamond instance (route provenance; unfunded route closed); `index_connectivity_does_not_imply_derivability` (bridges connect judgments, not indices) | zero-axiom core; instances ≤ propext |
| `StructuralPolicySequent` | `ContextPolicy` (read-discipline parameterization, honestly scoped); `PEntail` with threaded residuals; **the pricing pair** (`cartesian_contraction_free` / `linear_contraction_priced` / `linear_pay_twice`) + `linear_every_derivation_pays`; v4 stack re-proved parametrically; `pentail_cartesian_iff` collapse (S4 + diamond recovered) | zero-axiom core; linear pieces ≤ [propext, Quot.sound] |
| `EvidenceCalculusSequent` | `EvidenceCalculus` laws (`step_shape`: funding never widens — *the rule relation is the sole authority map*; `step_targets_evidence`: no derive-to-target bypass); `stamps_are_inherited_not_minted`; `derivation_funds_only_what_origin_funded` (existential inclusion, honestly scoped); **`eentail_iff_read_rooted`** (end-to-end capstone); `UniversalStamp`/`EvidenceCurrencyFree` screen + detection pair (fenced FORBIDDEN `stampSystem` caught; diamond clean) | zero-axiom enforcement core; instances ≤ propext |

## Screening honesty (carried in the files, binding on release notes)

- `MasterFree` is universal-hub **screening**, not anti-authority enforcement:
  false negative = evidence-currency master (addressed by
  `EvidenceCurrencyFree`); false positive = benign router (index screening
  over-approximates, by the campaign's own mismatch wall).
- `EvidenceCurrencyFree` screens **evidence shape** (the rule relation at the
  evidence position). Named false negative: broad-but-not-universal
  multi-currency evidence (consumer policy question).
- The closed-index wall over derived evidence carries a contract premise: the
  evidence calculus must respect the index set (`hstepclosed`).

## Named follow-ups (not claimed)

Full structural-rule algebra (split/merge/exchange/scope); full SEQ2/SEQ3
equivalence under the linear policy; multi-currency breadth budgets;
**v5: custody-preserving normalization** — *no normalization step may erase
custody evidence*; the read-rooted normal form is the invariant it must
preserve. Post-v4 v3.x coverage items (non-toy non-transfer targets,
`MustSurvive` parameterization, execution-custody actuator boundary) remain
queued in the campaign counter.

> v3 proved the family. v4 proves the crossings. v5 must prove the
> normalization doesn't launder what the crossings paid for.
