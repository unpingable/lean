# PJ Tranche C-prime Theorem Inventory

Date: 2026-07-22

## Executable surface

C-prime adds 39 compiled declarations in two isolated modules. Every one is
axiom-free. The direct qualification leaf prints 29 central declarations, all
axiom-free.

No declaration is added to `PJ/Core.lean`. No generic owner, institution,
context-transport record, residual carrier, or frontier is defined.

## Ownership boundary receipts (12)

### Generic absence-of-state boundary

- `PJ.TrancheCPrime.Ownership.duplicateEntitlement`
- `PJ.TrancheCPrime.Ownership.consumeSameEntitlementTwice`

These constructions show that PJ entitlement is reusable proof and that the
B-prime consumer is pure. They do not claim repeated execution.

### GT

- `GovernedTransport.repeatedExactRouteEvidence`
- `GovernedTransport.bridge_description_does_not_realize_missing_route`

### Execution Custody

- `ExecutionCustody.repeatedAttemptEvidence`
- `ExecutionCustody.spent_stage_does_not_supply_execution`
- `ExecutionCustody.bridge_schema_does_not_realize_attempt`

### Someone Continuity

- `SomeoneContinuity.repeatedReachabilityEvidence`
- `SomeoneContinuity.breach_reuses_exact_packet_after_demotion`
- `SomeoneContinuity.local_packet_ownership_does_not_supply_cross_agent_receipt`

### StaticRole held-out

- `StaticRole.repeatedFunctionalEvidence`
- `StaticRole.lawful_action_does_not_supply_functional_uptake`

## Context/noncommutation receipts (17)

### GT

- `GovernedTransport.firstRepairExtension`
- `GovernedTransport.oldRouteIntoRepair`
- `GovernedTransport.repair_is_not_old_context_equivalence`
- `GovernedTransport.repair_changes_qualification_geometry`

The native `CoverageExtension` is load-bearing: it embeds every old route
while exact non-equivalence proves that repair is not an invertible context
rename.

### Execution Custody

- `ExecutionCustody.different_prestate_may_commit`
- `ExecutionCustody.different_prestate_commit_attempted`
- `ExecutionCustody.differentPrestateEntitlement`
- `ExecutionCustody.old_stage_permission_not_entitled_at_different_prestate`
- `ExecutionCustody.exact_stage_receipts_do_not_reindex`

These are exact index-separation results. They do not assert a temporal
transition, history, or current authority between the two stages.

### Someone Continuity

- `SomeoneContinuity.foreignCandidateRejectsToGwen`
- `SomeoneContinuity.john_and_gwen_indices_are_distinct`
- `SomeoneContinuity.foreign_candidate_does_not_own_packet`
- `SomeoneContinuity.reachability_does_not_reflect_source_packet_ownership`
- `SomeoneContinuity.reachable_context_preserves_agent_id`
- `SomeoneContinuity.changing_agent_index_leaves_reachable_fragment`

These retain native one-way preservation and its failure of reflection.

### StaticRole held-out

- `StaticRole.exact_isomorphism_conditionally_preserves_and_reflects_r3`
- `StaticRole.presentation_change_is_load_bearing_noncommutation`

The first requires the exact full-signature and uptake-layer isomorphisms. The
second keeps R2 and the evaluator fixed while lawful presentation wiring
changes R3.

## Compiled declaration and axiom footprint

- 553 compiled owned declarations across eleven exact PJ modules;
- 533 axiom-free;
- 20 exactly `[propext]`, all inherited from pre-C-prime modules;
- 39 compiled C-prime declarations, all axiom-free;
- 29 named central C-prime receipts, all axiom-free;
- zero `Quot.sound`, `Classical.choice`, other, or mixed footprints.

Declaration-manifest SHA-256:
`09c203d95157afb0ef379668f64753a9e74fb22c7e2387c8efde7c5e5d4821ab`.
