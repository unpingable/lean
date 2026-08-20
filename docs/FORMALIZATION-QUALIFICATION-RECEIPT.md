# Nightshift → AG formalization qualification receipt

This receipt records the completed F1–F4 formalization of the frozen
Nightshift → AG governed-authorization contract. It is a bounded
runtime-correspondence qualification, not an architecture specification.

## Runtime pins

```text
Nightshift: a62686c61ac092f2167c68ed7db69c06d3439b47
AG:         707a2ee3a591dfe234ee8919257e62b3bf6831db
```

Source contract: `nightshift/docs/CANONICAL_RUNTIME_C1.md`
Handoff: `nightshift/docs/working/decisions/FORMALIZATION-HANDOFF.md`

## F1 — spend gating

- Theorem family: authorization-time spend gates, proposal/admissibility
  inertness, and one-use authorization discipline.
- Independent Kimi audit: correspondence holds with non-blocking
  clarifications.
- Axioms: the principal F1 theorems depend on no axioms.

## F2 — provenance and no silent rebinding

- Theorem family: evidence-basis pinning, current catalog-policy provenance,
  standing-resolution and mandate provenance, and exact-work binding.
- Independent Kimi audit: correspondence holds with non-blocking
  clarifications.
- Axioms: the principal F2 theorems depend on no axioms.

## F3 — DecisionBasis adequacy

- Decision-relative adequacy for the complete current
  `WorkPreconditionV1` family.
- Source domain: 15 states.
- Predicate family: 6,561 predicates.
- Source-level comparisons: 98,415.
- Unsafe collisions: 0.
- Independent Kimi audit: correspondence holds with non-blocking
  clarifications.
- Axioms: the finite adequacy certificate and production theorem depend on
  `propext` and `Quot.sound`; no semantic axiom or `native_decide` is used.

Adequacy is decision-relative, not injectivity.

## F4 — observation currentness and lineage

- Theorem family: five-field family-scoped lineage, lexicographic logical
  ordering, the exclusive freshness boundary, stale-before-superseded status,
  the currentness-to-usability adapter, and stale/superseded no-spend
  composition through F1/F2.
- Independent Kimi audit: correspondence holds with non-blocking
  clarifications.
- Axioms: structural supersession and monotonicity theorems are axiom-free;
  reflected status/adapter and composed no-spend theorems use at most
  `propext` and `Quot.sound`. No semantic axiom or `native_decide` is used.

## Environmental assumptions

- source/resolver honesty;
- request-sealer integrity;
- `evaluated_at` adequacy;
- standing authority honesty;
- revocation timeliness;
- upstream admission;
- digest collision resistance;
- deployment configuration.

## Nonclaims

- no proof of external-world truth;
- no proof of resolver honesty;
- no proof of SHA collision impossibility;
- no liveness claim;
- no universal Clean rule;
- no injectivity requirement.

Formalization tranche complete.
No further formal work is scheduled in this tranche.
