# PJ-A — Held-Out StaticRole Test

Date: 2026-07-22

## Disposition

`FAITHFUL-PARTIAL-INSTANCE-WITH-LOCAL-FUNCTIONAL-DEPENDENCE-EXTENSION`

StaticRole's ratified R0--R3 ladder is an exact instance of the frozen PJ
indexed-judgment/receipt bridge at each oriented rung. StaticRole as a whole
is not absorbed by the PJ core: its lawful reference action, de-se erasure,
evaluation, factorization, alternate lawful presentation, and correctness
laws remain an irreducible local functional-dependence extension.

This held-out result did not revise the PJ signature.

## Frozen test conditions

StaticRole was held out during PJ-0 and PJ-1. Its implementation was inspected
only after the three primary adapters compiled against the frozen core.

- StaticRole phase-three candidate:
  `63367a9f488a7ecbaf369c929b4becfd3ad60022`
- candidate tree:
  `155dfe3fd33869878723b14fbca85394ba560c26`
- candidate parent / phase-two ratification:
  `63d54e777e2670866806e1a7ee30798e55f3aae9`
- StaticRole phase-three operator ratification:
  `0dc621b782b0898152e325633cad1fbcb33b2f01`
- ratification tree:
  `f7ff0342aacfc4f0998ebacfd2c3b6b95b748b98`
- frozen PJ core:
  `PJ/Core.lean`
- frozen PJ core SHA-256:
  `1d86bee97f92f2644d8605a05d6a31deaa3584f55582d4a09b638718ffff185c`

The held-out adapter is `PJ/HeldOut/StaticRole.lean`. The core hash remained
exact before and after the held-out implementation. No StaticRole definition,
theorem, candidate, or ratification record was modified.

## Exact rung mappings

All bridge indices are exact pairs of StaticRole centers. `SameCenters`
provides only equality between the source and target center pair; it does not
store a rung conclusion.

### Native downward projections

| PJ bridge | Source judgment | Target judgment | Exact native content |
|---|---|---|---|
| `r1ToR0ProjectionBridge` | R1 `InternalRoleEncoding` | R0 `ExternalRoleShift` | consumes the R1 conjunction and returns its native R0 component |
| `r2ToR1ProjectionBridge` | R2 `ProspectiveDeSeEncoding` | R1 `InternalRoleEncoding` | consumes the R2 conjunction and returns its native R1 component |
| `r3ToR2ProjectionBridge` | R3 `FunctionalUptake` | R2 `ProspectiveDeSeEncoding` | invokes native `functional_uptake_implies_r2` |

These projections do not supply an upward rung.

### Evidence-bearing upward bridges

| PJ bridge | Source judgment | Receipt evidence not present in the source | Target judgment |
|---|---|---|---|
| `r0ToR1Bridge` | R0 | four exact internally hosted role cells | R1 |
| `r1ToR2Bridge` | R1 | continuation, coherent current-reference preservation, exact forecast token, hosting, and grounding | R2 |
| `r2ToR3Bridge` | R2 | actual and alternate lawful inputs, exact transported-reference binding, equal de-se erasure, distinct references, faithful presentation, and output discrimination | R3 |

No receipt stores its completed target judgment. In particular,
`R2ToR3Receipt` contains concrete lawful inputs, presentation equalities, and
an output inequality rather than a Boolean or proposition asserting that
functional uptake occurred.

The three inhabited entitlement values
`coherenceR0ToR1Entitlement`, `coherenceR1ToR2Entitlement`, and
`coherenceR2ToR3Entitlement` recover the native R1, R2, and R3 judgments
through `EntitledFrom.targetEvidence`.

## Strictness retained

The adapter carries all three rung boundaries through exact PJ
anti-entitlement:

- `r0_without_r1_remains_not_entitled` retains external role shift while the
  internal role cells needed for R1 remain absent;
- `r1_without_r2_remains_not_entitled` retains the complete R1 structure while
  `fixedAction` lacks designated-current-reference preservation and therefore
  supplies no R2 entitlement;
- `r2_without_r3_remains_not_entitled` retains the complete R2 judgment while
  `neutralizingUptake` supplies no R3 entitlement.

The held-out result therefore does not turn the ladder into automatic
implication in the upward direction.

## Local extension boundary

The following exact StaticRole laws are retained by the held-out module but
are not promoted to `PJ.Core`:

- `lawful_reference_transport_boundary` retains coherent reference action and
  the native node-level `CoherentProspectiveWitness`;
- `same_reduct_presentation_boundary` retains one R2 reduct and one evaluator
  with alternate lawful presentation wiring and opposite R3 results;
- `factorization_boundary` distinguishes faithful uptake from neutralizing
  uptake by failure versus satisfaction of factorization through exact de-se
  erasure;
- `correctness_boundary` preserves independence between functional dependence
  and output correctness;
- `availability_and_consumption_boundaries` preserves availability without
  faithful consumption and forecast consumption without de-se-dependent
  uptake.

These results require StaticRole-local reference coordinates, an evaluator,
erasure, presentation laws, and controlled output discrimination. None was
forced by Governed Transport, Execution Custody, or Someone Continuity during
PJ-1. Adding them after the held-out test would contaminate the frozen common
core with held-out semantics.

## Declaration and axiom audit

The held-out module explicitly audits 15 declarations:

- six bridge values;
- one positive entitlement-recovery theorem;
- three strict-rung anti-entitlement theorems;
- five local-boundary theorems.

All 15 are axiom-free. The module introduces no custom axiom, `Classical`,
`Classical.choice`, quotient dependency, `sorry`, or stored conclusion field.

## Held-out conclusion

StaticRole validates the minimal PJ substrate without making the current
common theory larger. Its R0--R3 edges are exact indexed, receipt-bearing
bridges, and its hostile rung boundaries remain hostile. Its richer
functional-dependence theory remains local.

This supports a shared substrate while constraining any later claim that PJ
already contains a generic theory of evaluation, de-se erasure,
factorization, same-reduct presentation, or correctness independence.
