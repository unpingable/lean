# 8. Boundaries, countermodels, and nonclaims

The public theory is easiest to overstate at its seams. This chapter states the
limits as part of the mathematics rather than as release trivia.

## Exact nonclaims

1. **No universal process semantics.** `GovernedFamily` defines claims,
   evidence, books, and a total decision. It defines no process, transition
   relation, scheduler, or trace semantics. Other repository modules may define
   such objects, but the calculus root does not unify them. The crossing core
   explicitly defines no transition system
   ([scope fence](../../LeanProofs/Admissibility/Calculus/Crossing.lean#L37)).

2. **No global `Admissible`.** Weathering's `Admissible` is its native licensing
   judgment. Paid reachability and BreakGlass keep different native substrates.
   The common predicate is derived `Authority F c`, always parameterized by a
   governed family and claim.

3. **No runtime enforcement or conformance claim.** A Lean checker definition
   does not prove that a deployed runtime called it, preserved its evidence, or
   mapped runtime objects correctly. The stable-root header lists the additional
   correspondence artifacts required
   ([source](../../LeanProofs/Admissibility/Calculus.lean#L29)).

4. **No automatic composition of all kernels.** The public crossing is binary
   and requires two `GovernedFamily` values with lossless refusal spines. It does
   not absorb the eight older admissibility kernels, all repository calculi, or
   arbitrary N-ary families. The separate kernels root disclaims a unified
   maximal calculus
   ([source](../../LeanProofs/Admissibility/AdmissibilityKernels.lean#L61)).

5. **No universal subsumption theorem.** The public comparison framework has
   seven indices and proof-bearing law shapes, but the concrete seven-entry
   ledger remains outside the public Lean surface. `Ledger.covers` is a theorem
   about any supplied ledger, not a public inhabitant containing those seven
   native comparisons.

6. **No silent promotion of annex material.** Hostile audits, counterexamples,
   legacy exploits, concrete comparison adapters, and blocked predecessor
   packets retained in skunkworks are evidence about the admitted surface; they
   are not imported declarations. The definitive per-rung list is the
   [v14 readiness ledger](../V14-READINESS-LEDGER.md).

## Countermodels and hostile controls

Some negative evidence is public as a generic theorem; some remains annexed:

| Boundary | Public result | Annex/adverse evidence |
|---|---|---|
| claim erasure | `no_claim_erasing_check_is_faithful` | Prop-squashing and full-claim controls |
| refusal encoding | no subsingleton exact domain | compiled constant-`Unit` collapse against the old contract |
| comparison exactness | collapsed/constant maps reject exact representation | instantiated seven-entry ledger and adapters |
| stored crossing | exact stored-pair coherence and non-shadowing | arbitrary-stored-pair hostile audit; legacy crossings |
| BreakGlass | origin-bound family, two separations, stored crossing | 49-receipt hostile matrix, fixed-`Atoms` exploit, blocked predecessor packet |

The custody assignments in this table come from
[claim-register entries 20–25](../../CLAIM-REGISTER.md#20-v14-rung-2--governed-family-signature)
and the [readiness ledger](../V14-READINESS-LEDGER.md), not from inference based
on filenames.

## Deliberate weakenings required by the source

- “Lossless decisions” is too broad. Only refusal packets are losslessly
  encoded into the spine; accepted witness identity is not serialized.
- “Paid discharge” is too strong for the public bounded-paid fixture. Its
  positive run is admission-only, custody is vacuous, and obligations are
  empty.
- “Locations authenticate origin” is too strong. `foldLocated` soundly carries
  input labels, but raw labels and arbitrary relabeling are not authenticated.
- “Exact comparison” is ambiguous. The code distinguishes exact *judgment*
  from exact *representation*.
- “BreakGlass crosses into ordinary authority” is false. The public result is a
  separation: exceptional authority coexists with a retained denied ordinary
  verdict.
- “BreakGlass lifecycle is general” is false. It is relative to supplied
  `Atoms`, uses a bounded singleton audit trail, and proves no general
  transition universe, payment lifecycle, clock honesty, origin allocator, or
  cryptographic commitment.

## Axiom posture

The calculus is not uniformly axiom-free. Rungs 2–6 have the precise footprints
listed by the calculus gate; rung 7 deliberately includes `Quot.sound`,
`Classical.choice`, and the declared opaque public substrate. The operator
accepted that footprint at ratification. The exact 101-receipt rung-7 split is
recorded in the
[readiness ledger](../V14-READINESS-LEDGER.md#rung-7--the-originhistory-bound-breakglass-terminal-instance-admitted-2026-07-18)
and enforced theorem-by-theorem by
[`check-calculus-footprint.sh`](../../scripts/check-calculus-footprint.sh).
