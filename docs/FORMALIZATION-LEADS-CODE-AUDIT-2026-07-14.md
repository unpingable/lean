# Formalization Leads Code — Cross-Repository Verbiage Audit

**Status:** completed for the writable Lean repository on 2026-07-14;
follow-up inventoried for read-only sibling repositories.

## Governing rule

Formalization may begin from a coherent claim, countermodel, or specification
before any runtime consumer exists. Lean establishes the contract and may lead
subsequent implementation. A consumer can provide an instantiation or runtime
correspondence test; it never grants permission to state, compile, or develop a
theorem.

Opening formal work is governed by intrinsic criteria: a precise
non-tautological statement, honest hypotheses, overlap review, and bounded
scope. Completed proofs and disclosed axioms govern discharge and promotion.
Public custody, compatibility promises, tags, and releases require their own
explicit decisions and may consider runtime evidence. Citation/adoption names
the intended contract; a runtime-conformance claim requires an explicit mapping
plus runtime evidence or a refinement proof.

## Lean repository corrections

The active contradictions were corrected in this repository:

- `README.md` and `LeanProofs/Admissibility/README.md` now state the governing
  rule and separate formalization, custody, and runtime conformance.
- `docs/NEXT-SURFACES.md`, the bounded-calculi roadmap, frontier register,
  release ledger, crosswalks, claim register, and semantic audit no longer use
  runtime arrival as formalization admission.
- Candidate and Scratch headers now state that formalization does not wait on
  runtimes, while retaining runtime correspondence evidence as a separate
  promotion condition where the existing custody rule requires it.
- `Corrective`, `AxisSkew`, `SafetyBridge`, `LocalBoundary`,
  `SurfaceAuthorization`, and `PublicReceiptRefinement` now identify the real
  formal debts: nondegenerate semantics, explicit bridge assumptions,
  separating models, and honest evidence predicates.
- Counterexample-family and anti-vacuity gates remain, but are no longer called
  forcing-case discipline.

Historical filenames and explicitly dated changelog records remain intact;
where a dated audit could still be mistaken for current policy, it carries a
supersession note.

## Papers repository follow-up (read-only here)

The highest-priority direct inversions are:

- `working/tooltheory/admission-gate-claim-conversion-normal-form.md:127`
- `preprint/27-obligation-unsound-reconciliation/WORKED_CASES.md:3`
- `preprint/27-obligation-unsound-reconciliation/obligation_unsound_reconciliation.md:282`
- `working/tooltheory/byzantine-fault-tolerance-extension.md:83`
- `working/tooltheory/nq-forcing-case-audit.md:3`
- `working/excavation-vs-yagni.md:9`
- `working/anti-laundering-doctrine-map.md:146`
- `working/laundering-move-watchlist.md:145`
- `docs/formalization-backfill-notes.md:111`

These notes variously require running code, a shipping blocker, a downstream
consumer, or repeated cases before Lean may be built. Current-policy text
should be rewritten directly. Dated audit/provenance text should instead get a
banner: **historical formalization gate; superseded 2026-07-14**.

Several notes are also factually stale after the papers-fragment extraction:
the consolidation controller, commitment standing, Signal Authority, status
conversion, affective coupling, and silent-projection notes still describe
their Lean artifacts as absent. The exact extraction/status audit is in
`docs/PAPERS-LEAN-FRAGMENT-AUDIT-2026-07-14.md`.

## Other sibling repositories (read-only here)

### `~/git/transition-kernel`

Current contradictions:

- `SUMMIT.md:59`
- `docs/NON_CORRESPONDENCE.md:77`
- `docs/CORRESPONDENCE.md:68`
- `docs/LEAN_OBLIGATIONS.md:45`
- `src/composed_snapshot.rs:19`

These say a deployed operational gate must precede or justify a Lean theorem.
Keep the valid proof-to-world fence—a green Lean build does not prove Rust
conformance—but reverse the development order: Lean may state the abstract
invariant first; an explicit mapping plus deployment evidence or a refinement
proof may later discharge correspondence.

### `~/git/research`

`candidate-intake-protocol.md:79` says a partial finding gets “no Lean until a
consumer forces it.” Replace that with a narrow formal-residue rule: formalize
when the proposition is well-posed; consumer evidence governs only product or
correspondence claims.

### `~/git/skunkworks`

Current living-policy contradictions occur in:

- `patterns/admissibility-and-standing.md:401`
- `patterns/constitutional-stack.md:112`

The formalization journal also contains dated consumer gates in
`formalization/new-ideas-lean4.md` and
`formalization/FORMALIZATION_REPOSITORY_AUDIT_2026-07-14.md`. Preserve those as
provenance with one journal-wide supersession banner. This worktree already
contains unrelated edits and new files, so it should be reconciled deliberately
rather than batch-rewritten.

### `~/git/playground`

This is a stale, dirty mirror of many Lean files. Its copies of
`Admissibility/README.md`, `Corrective`, `SafetyBridge`, `ParameterizedMerge`,
`BoundaryWitness`, and related modules retain the old gates. Reconcile from the
canonical `~/git/lean` wording without overwriting its unrelated worktree.

No material formalization blockers were found in the surveyed `agent_gov`,
Nightshift, WLP, linearaccountant, Porter, or continuity repositories. Their
similar language generally gates runtime deployment or claims of operational
conformance, which remains legitimate.
