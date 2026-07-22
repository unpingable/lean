# What this is

This is a Lean 4 proof workbench for **governed computation**: formal models of
when evidence licenses a conclusion or state transition, and when standing,
custody, authority, spend, history, refusal, or obligation remains an
independent condition.

It does not primarily formalize proofs about proofs or the act of
formalization. It formalizes the admissibility of consequential judgments and
transitions. Proof-producing checkers and evidence data are governed objects
inside that subject, not the subject's replacement.

The central question is not merely “can the machine take this transition?” It
is:

> What exact evidence justifies this judgment, at these indices, under this
> actor's standing and custody—and what remains unresolved afterward?

That question is useful in authority-bearing, externally consequential
systems. A reachable endpoint can have an unlawful history. Custody can exist
without authority. Standing can coexist with refusal. A successful and safe
effect can leave an obligation undisclosed or undischarged. In the modules
that store native decisions, replaying their projections preserves the stored
result without earning a fresh receipt.

Most modules follow a small formal-methods pattern:

1. state a bounded judgment or transition model;
2. identify the evidence and indices that support it;
3. make the tempting stronger inference explicit; and
4. prove the permitted bridge or exhibit a countermodel to the invalid one.

The unusual words name different mathematical objects. A `Witness` is
evidence indexed by a particular claim. A `Refusal` is structured evidence for
non-admission, not a bare Boolean. `Standing` concerns the claim's basis;
`Custody` concerns provenance intactness; `Spend` is family-native resource
consumption; and `Obligation` concerns what remains live after action. A
hostile countermodel is deliberately qualified against a tempting semantic
lift: it retains plausible neighboring premises while refuting the stronger
conclusion. The [semantic guardrail table](README.md#semantic-guardrails)
records the exact orientation and prohibited reductions.

## The public calculi

The repository contains several independently scoped formal families. The v14
Governed Admissibility Calculus supplies claim-indexed witness/refusal data,
separate standing/custody/obligation books, bounded instances, exact refusal
encodings, stored decisions, and an origin/history-sensitive BreakGlass
instance.

V15 adds a Cross-Calculus Atlas over selected edges from Governed Transport,
Execution Custody, and Continuity Admission. The mappings preserve the native
indices and exact receipts required by those edges. They do not identify the
three calculi, translate every theorem, or create a shared algebra. StaticRole
is a held-out partial instance closed at R3; Inquiry and Preparation remain
independent comparison-only neighbors.

Governed Transport is not defined as a morphism. Its `Span` is only bare
proof-relevant crossing geometry; certificate-dependent lift, translation,
and target-local reliance are separate types, and the span itself supplies no
authority law. A categorical model could describe some structure only after
these governed distinctions and their omissions are kept explicit.

The bounded `BreakGlass` instance is likewise not an axiom. It constructs an
exceptional permit and origin-bound attempt, commit, execution receipt,
obligation, audit record, and settlement lifecycle. Exceptional authority does
not silently become ordinary authorization or clean history.

## What this is not

This is not a blockchain or cryptocurrency protocol, zero-knowledge system,
legal-evidence product or legal protocol, smart-contract framework, generic
audit-log implementation, category-theory library, generic state-machine
verification project, or alternate-reality game. Nor is it a relabeling of
ordinary proof theory or programming-languages metatheory. Those areas may
instantiate or orient some formal structures in the repository, but none
supplies its definition or intended classification. The public records are
ordinary source and verification receipts, not an interactive reveal.

It is also not a universal theory of institutions, a complete model of
machine judgment, a JCP implementation, an operational AG/NQ realization, or
a claim that every governed process reduces to one calculus.

## Formal result versus deployed system

Lean checks the theorems under their disclosed definitions, hypotheses, and
axiom footprints. It does not prove that a runtime implements them. A runtime
conformance claim requires a separately scoped correspondence map, executable
preservation evidence, and revision-bound qualification receipts for every
governed distinction.

For the first technical orientation and an end-to-end example, read the
[`plain-language summary`](docs/PLAIN-LANGUAGE-SUMMARY.md). For exact theorem
scope, read [`WHAT-THIS-PROVES.md`](WHAT-THIS-PROVES.md). The source and build
commands are in the [`README`](README.md).
