# 9. Reading the Lean

This chapter assumes the terminology introduced in chapters 1–8. The
[glossary](glossary.md) gives compact definitions when reading modules out of
order.

## Start from the root, not a search result

The exact root is
[`LeanProofs/Admissibility/Calculus.lean`](../../LeanProofs/Admissibility/Calculus.lean).
Its imports determine the public compatibility surface, called a **stable
root** in this repository. A suggestively named declaration elsewhere is not
thereby part of this calculus.

Read in dependency order:

```text
PathVerdict.Core ← Edges ← Domains
                         ← Located

Calculus.Core
  ├─ native instances
  ├─ Spine + exact instance spines
  ├─ Comparison
  └─ Crossing
       ├─ Weathering × bounded paid
       └─ Weathering × BreakGlass

BreakGlass.LifecycleOrigin → Native → Lifecycle → governed instance
                                                → Spine / Comparison / Crossing
```

The actual imported graph is checked mechanically; this diagram is explanatory,
not an alternate root definition.

## Recognize the kinds of declarations

- A **structure field** in `GovernedFamily` is an assumption every instance
  must provide.
- A **definition** such as `Authority` fixes meaning by reduction.
- A **theorem** derives a consequence from fields and earlier results.
- A family's **`decide`** field is executable checkability, but not necessarily
  general search.
- A **witness** or **refusal** is native data returned by that decision.
The `#print axioms` commands at module tails are audit probes. The scripts check
their exact reported footprints; the probes are not additional mathematical
theorems.

### Repository metadata

A **custody header**, registry row, or ledger statement is a repository-level
assertion about publication and compatibility, not an object-level theorem.
Mathematical custody (`F.Custody c`) is a different, claim-indexed predicate.

## Namespaces that should not be collapsed

- `Admissibility.Calculus.GovernedFamily.Authority` is witness existence for a
  governed family.
- `Admissibility.PathVerdict.PathVerdict.AuthorityBearing` is emptiness of an
  obstruction log.
- `Admissibility.Calculus.Crossing.Authority` is existence of a paired native
  crossing witness.
- `Admissibility.Authority.AuthorityVerdict` belongs to the older authority
  kernel and is used as a retained native coordinate inside BreakGlass.

Theorems relate these notions at explicit seams. They are not definitionally
one global authority concept.

## How to audit a prose claim

1. Follow its declaration link and inspect the full type.
2. Check whether the premise is an assumption, a stored decision, or a derived
   judgment.
3. Check the namespace and family parameters.
4. Check whether the result is an implication or an equivalence.
5. Check whether evidence identity survives or has been squashed to `Nonempty`
   or `Bool.isLeft`.
6. Check the module's custody role in
   [`public-custody.tsv`](../../scripts/public-custody.tsv) and ownership in
   [`stable-surfaces.tsv`](../../scripts/stable-surfaces.tsv).
7. Check the axiom gate before calling a theorem axiom-free.

## Mechanical verification

The documentation uses repository-relative `path#Lline` links. This repository
currently has no dedicated documentation-validation command, so editorial
changes must resolve those links directly and then run the relevant existing
Lean and audit gates. The stable mathematical gates are:

```bash
lake build
lake build AdmissibilityCalculus PathVerdict PathVerdictEvidence
bash scripts/check-pathverdict-footprint.sh
bash scripts/check-calculus-footprint.sh
bash scripts/audit-axioms.sh
bash scripts/check-custody-classes.sh
bash scripts/check-mathlib-free-targets.sh
```

The bare exit status, not selected output, determines success.
