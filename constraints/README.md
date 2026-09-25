# Design constraints

These are formal results used to constrain design claims. They are not a
formal verification of Constellation or ABSD as whole systems.

Each module proves a small, general statement about what one kind of
evidence does and does not license, and says in its header what it does NOT
establish. The modules are Mathlib-free, import nothing outside this
directory, and are public evidence (Lake target `DesignConstraints`), not a
stable compatibility surface.

| Module | Establishes | Named results |
| --- | --- | --- |
| [`DecisionSemantics/Quantization.lean`](DecisionSemantics/Quantization.lean) | Equal quantized observations do not imply equal latent values; the exact licensing assumption is faithfulness (equivalently, a decoder), and a collision refutes it. Truncating and decimal quantizers collide at any coarser-than-unit resolution. | `observed_equality_not_latent_equality`, `no_decoder_of_collision`, `collision_blocks_predicate_transport`, `truncatingQuantizer_not_faithful`, `decimalQuantizer_collision` |
| [`DecisionSemantics/Perturbation.lean`](DecisionSemantics/Perturbation.lean) | Two perturbations at equal total-variation distance from one base distribution select opposite options under every argmax-style rule, with unique maximizers throughout; no function of (base weighting, distance) determines the decision. | `equal_magnitude_opposite_decisions`, `equal_magnitude_preserves_and_reverses`, `no_magnitudeOnly_attribution` |
| [`DecisionSemantics/InterfaceCoherence.lean`](DecisionSemantics/InterfaceCoherence.lean) | When a response carries both a reported choice and the weights, "the choice is some maximizer" does not make trusting the choice and recomputing it agree; agreement is exactly coherence with a designated rule, and the rule must be named. Without a top tie, any argmax rule closes the gap. | `agree_iff_ruleCoherent`, `maximizerCoherent_permits_disagreement`, `coherence_is_rule_relative`, `agree_of_maximizerCoherent_of_noTopTie`, `argmaxRule_necessary_for_noTopTie_agreement` |
| [`Resources/ObligationViability.lean`](Resources/ObligationViability.lean) | A run can obey its admitted budget and fit the available capacity yet leave too little for a mandatory obligation. For one additive resource with no replenishment, `spend + requiredReserve ≤ available` is sufficient for the residual state to be viable. | `budget_compliance_does_not_imply_viability`, `preserves_required_reserve_implies_viable`, `compliant_execution_viable_of_reserve` |
| [`Authority/ProvenanceIsNotAuthority.lean`](Authority/ProvenanceIsNotAuthority.lean) | Over a ledger where admission is the only introduction rule for authority: provenance composes along chains, authority is exactly admission at the object, and no chain to an admitted origin (or from an admitted descendant) confers authority on an unadmitted object. | `descent_is_transitive`, `authority_iff_admitted`, `authority_is_not_heritable`, `authority_does_not_flow_upstream`, `admission_does_not_leak` |

## What these results are for

Each module is cited by a design claim, and the claim is only as strong as
the theorem's stated scope:

- `Quantization` and `Perturbation` fix what a consumer of a decision
  interface may conclude from a rounded score or from "how far the
  distribution moved". They are about arbitrary functions and finite weight
  vectors; they say nothing about any model, provider, or calibration.
- `InterfaceCoherence` fixes the invariant a consumer needs before reading a
  reported choice and recomputing it from weights interchangeably.
- `ObligationViability` separates a spend limit from the reserve needed to
  finish mandatory obligations. It is the formal form of the statement
  "staying within budget can still leave work unfinished". It is a scalar
  bridge; it does not prove that any budget controller performs the reserve
  check.
- `ProvenanceIsNotAuthority` fixes "parentage is not authority" and "a record
  of production is not a verdict" as one statement about an abstract ledger.
  A system whose authority is issued only by explicit admission instantiates
  it; the module does not show that any system does.

## Build and check

```bash
lake build DesignConstraints
bash constraints/check.sh
```

`check.sh` builds the target, refuses `sorry`, local axioms, `native_decide`
and other non-kernel constructs, requires that no module imports anything
outside this directory, and re-attests the axiom footprint of all 63 named
declarations: 34 are axiom-free, the rest use only `propext` and, in one
case, `Quot.sound`. No `Classical.choice`.

## Provenance

These modules were extracted from a private incubation tree. The statements
and proofs are reproduced without change; the namespaces, headers and, in
`Authority/`, the declaration names were rewritten so that the files can be
read without that history. Nothing here depends on it.
