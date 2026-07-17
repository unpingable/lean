# Adjudication Provenance — design note

**Status: OPEN DESIGN NOTE / NON-BINDING.** Filed 2026-07-14 from an
operator + ChatGPT formulation and a Codex overlap audit against the resident
Lean corpus. It states a possible successor seam but is neither a Lean module
nor public evidence for a completed theorem family. Formal work may begin when
the statement is precise, non-tautological, scoped, and overlap-audited;
promotion, versioning, tags, and DOI actions remain separate decisions.

The v13 custody migration retired ANNEX/Scratch as live repository lanes.
Historical paths below are identified explicitly; current public foundations
use their stable/evidence homes, while unfinished applications belong in
skunkworks. See [`V13-MIGRATION-LEDGER.md`](V13-MIGRATION-LEDGER.md).

## 1. Keeper and exact scope

The motivating slogan is:

> A judgment is only as portable as its warrant.

Its defensible formal content is narrower:

> A judgment is portable through a representation only when its verdict is
> constant on every fiber that representation collapses.

Negative diagnostic:

> A provenance coordinate is proved necessary for verdict preservation when
> erasing it merges worlds with different verdicts.

This is not provenance maximalism. A context coordinate does not earn carriage
merely by being available. It is load-bearing only if changing it can change
the verdict while the claimed portable surface remains fixed.

For a contextual adjudication, take:

```text
World    = Context × PortableInput
surface  : World → PortableInput
verdict  : World → Verdict
```

where `PortableInput` includes the artifact and query. Holding the query fixed
is load-bearing: if two adjudicators answer different queries, their different
answers do not establish a provenance-detachment failure.

Safe context erasure is the existing view-semantics predicate:

```text
Determines surface verdict
```

That is exactly:

```text
surface left = surface right → verdict left = verdict right
```

The negative specimen supplies two worlds with the same complete portable
surface and different verdicts. From that pair, no representation constrained
to reveal no more than the surface can preserve the judgment:

```lean
sameSurface       : surface left = surface right
differentValidity : verdict left ≠ verdict right

∀ {PortableObservation : Type}
    (portable : View World PortableObservation),
  WithinDisclosureBound surface portable →
  ¬ Determines portable verdict
```

The proof is the v10 refinement sandwich in negative form. If `surface`
refines `portable`, equal surface values force equal portable values; if
`portable` determines the verdict, those equal values force equal verdicts,
contradicting the specimen.

This quantification over every surface-bounded intermediate representation is
the factorization impossibility. Merely writing `Judgment Γ p` would not earn
it.

Within this scope, warrant detachment is projection laundering applied to
judgments.

## 2. Existing mathematical home

No `UniversalWarrantCalculus` is required. The generic theorem already lives
in the vocabulary of:

- `LeanProofs/ViewSemantics/Core.lean`: `View`, `Refines`, `Determines`, and
  `NotFullyDetermining`;
- `LeanProofs/ViewSemantics/BoundedProjection.lean`:
  `WithinDisclosureBound`, the refinement sandwich, and the exact compatible
  projection boundary;
- `LeanProofs/Admissibility/ConsequencePartition.lean`: the established
  projection/factorization face;
- `LeanProofs/ViewSemantics/Adapters.lean`: the existing identification of
  consequence partitioning and witness invariance with view determination.

A literal context-free evaluator

```text
evaluate : PortableInput → Verdict
```

that reproduces every contextual verdict implies `Determines surface verdict`.
The negative result therefore needs no choice principle or decoder synthesis.
The positive converse must retain the v10 off-image fence: a total evaluator
requires an explicit factorization map. For the product projection above, an
inhabited `Context` supplies a chosen section and removes that obstruction; an
arbitrary view does not receive such a decoder for free.

## 3. Resident receipts and overlap fence

The proposed principle has already been forced independently in several
domains. Any future application must adapt these receipts rather than
re-prove them behind new nouns.

| Domain | Existing receipt | What it already establishes |
| --- | --- | --- |
| Consumer-relative verdicts | Historical v12 `LeanProofs/Scratch/ConsumerRelativeVerdict.lean`: `HasGlobalSection`, `has_global_section_iff_consumers_agree`, `no_global_section_when_consumers_disagree` | A context-free `Artifact → Verdict` exists exactly when consumers agree. The superseded source is preserved by the v12 tag/Git history, not live v13 source. |
| Prop-valued observer packet | Historical v12 `LeanProofs/Scratch/NoUniversalRoot.lean`: `has_global_section_iff_consumers_agree` | Earlier Prop-valued global-section form, likewise retained only in release/Git history. |
| Predicate custody | `Admissibility/PredicateWitnessSeparation.lean`: `satisfaction_does_not_determine_admissibility`, `no_satisfaction_bridge_to_admissibility` | Identical satisfaction surface, different admissibility; no function of the erased surface recovers it. |
| Evaluator semantics | `Admissibility/Derivation.lean`: `disagreement_persists` | Identical state, actor, and claim receive opposite verdicts under two evaluator environments. |
| Temporal warrant | `BoundedCalculi/TemporalCustody.lean`: `citation_time_validity_does_not_imply_execution_admissibility` | Historical citation validity can remain while the use-time warrant refuses execution. |
| Receipt snapshot | v12 `Scratch/ExecutionRevalidation.lean`, now in skunkworks: `lossy_receipt_cannot_pin_snapshot` | Two transitions with the same lossy receipt ran under different governing snapshots. |
| Projection laundering | `Admissibility/ProjectionLaundering.lean`: `projection_launders_deferral` | Erasing a custody predicate enables an artifact-only consequential route. |

These results make the synthesis plausible. They do not by themselves create a
new public surface. In particular, v10 determination subsumes the negative
global-section no-go. The exact existence equivalence additionally uses the
inhabited product-projection section described above. The historical theorem
is therefore an overlap receipt, not a demand for direct promotion or
restoration of deleted source.

## 4. The genuinely open seam

The corpus does not currently carry one coherent data-level adjudication
receipt tying together the proposed coordinates:

```text
AdjudicationReceipt {
    artifact_ref
    query
    decision_context_ref
    policy_ref
    policy_version
    history_cut_ref
    evidence_view_ref
    clock_basis_refs
    cut_selection_receipt
    evaluator_semantics_ref
    evaluator_version
    verdict
    derivation_ref
}
```

This sketch is a requirements list, not a proposed Lean structure. References
alone confer no trust, and a record with these fields but no laws would be
metadata cosplay.

The unmodeled piece is adjudication provenance as an operational object:

- which history cut and evidence view were evaluated;
- who was permitted to select that cut;
- which policy and evaluator semantics produced the verdict;
- which versions identify those semantics;
- which derivation or receipts make the evaluation inspectable.

## 5. What would earn an application

The following gates are necessary, not sufficient, for a future
`AdjudicationProvenance` application. None may be replaced by a populated
record literal.

### A. Coherence

The recorded verdict is proved equal to the result of the named evaluator over
the named artifact, query, policy, history cut, evidence view, clocks, and other
declared inputs. Evaluator identity/version must select actual semantics, not
serve as a decorative label.

### B. Negative necessity

For each coordinate claimed load-bearing, erase it and construct a same-surface,
different-verdict or same-receipt, different-governing-context pair. A field
that cannot produce such a split has not earned mandatory carriage.

The strongest generic receipt should factor through the bounded theorem above:
no surface-bounded repair can recover the lost distinction.

### C. Positive sufficiency

The complete receipt supports stable replay or comparison under explicitly
pinned semantics. This means replaying the named evaluator on the named inputs,
not promising that a historical verdict remains correct under future policy,
evidence, or evaluator versions.

### D. Consumption

An actual boundary consumes the coherent receipt when making or comparing a
consequential decision. A dashboard that merely displays the fields is not a
consumer. A formal application may proceed once the semantics and anti-vacuity
requirements below are fixed. Runtime implementation may follow that contract;
a runtime-conformance claim requires correspondence evidence, while promotion
requires a separate operator decision.

## 6. Anti-vacuity requirements

Any eventual Lean application must:

1. hold artifact and query fixed in its detachment specimen;
2. use a typed verdict with at least two inhabited outcomes;
3. make the evaluator semantics executable or otherwise extensionally pinned;
4. represent cut-selection authority with a real relation or receipt, never a
   bare identifier or `True` field;
5. factor at least two independently forced resident domains through the shared
   theorem;
6. include a positive coherent/replayable case so universal refusal is not the
   model;
7. preserve source custody and import direction rather than restoring every
   adjacent historical or skunkworks file to the public tree.

## 7. Explicit refusals

This design note does **not** claim:

- that every context coordinate belongs in every portable judgment;
- that provenance makes a verdict correct or its evaluator trustworthy;
- that recording a cut proves the selector was authorized to choose it;
- that provenance chains terminate or that a trusted base is automatically
  well-founded;
- that two different evaluator outputs are contradictory before artifact,
  query, and portable context are aligned;
- that Lean currently internalizes its own kernel, imports, axiom footprint,
  reduction behavior, or versioned proof environment.

The proof-environment analogy remains prose. `#print axioms` and the repository
audit scripts are metalevel inspection. An object-language sequent
`Γ ⊢ proposition` does not formalize a compiled Lean theorem surviving a kernel,
import, or axiom-environment change. That example is deferred until a genuine
versioned environment/liveness model exists.

## 8. Campaign and release boundary

If a later formal campaign clears the intrinsic opening criteria, its initial
home is skunkworks, plausibly as a ViewSemantics application rather than a new
foundation. The generic theorem alone earns no public promotion, version, or
DOI; the coherent typed receipt, coordinate-ablation results, positive replay
boundary, and real consumption would be the substantive work.

Until then, the durable finding is:

> No consequence-bearing judgment is portable independently of every context
> coordinate that can alter its verdict while leaving the claimed portable
> surface fixed.
