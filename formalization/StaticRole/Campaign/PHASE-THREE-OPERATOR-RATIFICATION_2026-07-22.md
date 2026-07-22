# StaticRole Phase Three — Operator Ratification

## Decision

```text
STATIC-ROLE-PHASE-THREE-RATIFIED
```

Ratification review date: `2026-07-22`

This record ratifies the exact candidate revision, not a branch name:

```text
candidate commit: 63367a9f488a7ecbaf369c929b4becfd3ad60022
candidate tree:   155dfe3fd33869878723b14fbca85394ba560c26
candidate parent: 63d54e777e2670866806e1a7ee30798e55f3aae9
changed paths:    9
```

The candidate parent is the exact phase-two ratification commit.  The
phase-two scientific candidate remains
`0a203e95ddf7f96f9f71a8e9d8b4b60bbde8a349`.  Neither phase-two object nor
the phase-three candidate was amended, squashed, rebased, or rewritten.

At review entry, the branch was `gt3-stage3-candidate-h11`, `HEAD` and tree
matched the pins above, and the tracked worktree and index were clean.
Pre-existing untracked sibling work under `nq-ng`, `ux-design`, and `new-new`
was recorded and left untouched.

## Eleven-gate findings

### 1. No hidden uptake conclusion

`ProspectiveFunctionalInput` contains only a reference and forecast; source and
target are type indices and the node is derived.  `UptakeLayer` contains only
an output carrier, presentation, forecast-erasure and lawfulness obligations,
and evaluation.  It contains no use, relevance, sensitivity, success,
dependence, or uptake field.

`FunctionalUptake` is an external predicate requiring R2, two lawful
same-erasure inputs, the canonical carried reference, reference inequality,
exact presentation, and concrete output inequality.  The rich witness stores
node-level observations and supplied-output inequality, not `FunctionalUptake`
or a free dependence assertion.

### 2. Literal same reduct

The critical positive and negative systems share literal values for the base,
information layer, representation layer, frame, coherent action, R2 receipt,
centers, forecast and grounding, input/output carriers, actual and alternate
inputs, evaluator, correctness criterion, and all non-presentation context.

`faithfulUptake` presents its input unchanged.  `neutralizingUptake` changes
only the reference to the ordinary, independently lawful and grounded `false`
member of the same target fiber while preserving the forecast.  It has no
chosen-center branch or stored expected output.  Both definitions use the
literal evaluator `fun _ _ input => input.reference`; equality is also proved
by `central_presentations_share_output_and_evaluator` using `rfl`.

### 3. Presentation lawfulness

Dependent indices retain source and target.  `present_erasure` retains the
forecast exactly, and `present_lawful` requires every supplied replacement to
remain hosted and grounded.  These laws refuse unrelated or ungrounded
coordinates but deliberately do not require exact-reference preservation.
That stronger judgment is the separately derived `FaithfullyConsumes` equation
and is required by R3 rather than stored by the interface.

Lawful reference-ignoring, forecast-only, and alternate-same-fiber
presentations are constructible.  An unrelated or ungrounded replacement is
not lawful.  Thus interface lawfulness is nontrivial but not conclusion-bearing.

### 4. De-se-specific discrimination

At fixed frame, action, source, and target, the input has only reference and
forecast data.  R3 requires the forecasts to agree, so reference is the only
varying computational coordinate.  Nodes, roles, stages, perspective, and
target are derived; proof terms, modes, grounding witnesses, R2 receipts, and
transport evidence cannot reach the evaluator.  The fixture therefore proves
reference-sensitive output discrimination, not merely that two opaque unequal
inputs can receive unequal outputs.

### 5. Erasure and non-factorization

`eraseDeSe` removes exactly the reference and retains the forecast; source and
target remain fixed by the input fiber and factorization theorem.  The proposed
factor ranges over every lawful input at that fixed source and target.  Constant,
forecast-only, and neutralizing layers construct explicit factors, so failure
is not automatic.

R3 supplies two lawful equal-erasure inputs with unequal runs and therefore
constructively refutes any forecast-only factor.  No function extensionality,
choice, or classical existence is used.  The result is correctly one-way:

```text
FunctionalUptake -> not FactorsThroughDeSeErasure
```

It does not claim that every non-factorization establishes R3.  A subsingleton
output makes R3 impossible; retaining the reference in the erasure or choosing
inputs with different erasures removes the controlled contradiction.

### 6. Non-definitional characterization

The forward implication of
`functional_uptake_iff_nontrivial_de_se_dependence` builds the node-level
receipt and stored R2 object.  The reverse implication recovers the canonical
carried reference and exact supplied-input identities from node and erasure
equalities.  `referenceNode_injective` is load-bearing in both recoveries; if
distinct reference coordinates could realize the same node, the proof would
not go through unchanged.

The witness's output inequality concerns concretely supplied inputs.  It cannot
be projected directly into R3 until node injectivity and input extensionality
recover exact self-presentation.  General presentation laws are not claimed to
be load-bearing in this biconditional because the witness records stronger
concrete node and erasure observations.

### 7. Correctness independence

Both directions use the one criterion:

```text
OutputCorrect output := output = false
```

The reference-sensitive R3 transition returns `true` and fails correctness.
The constant input-insensitive transition returns the correct `false` but
factors through erasure and has no R3.  Correctness is absent from R3, and no
rationality, successful prediction, or successful action claim is inferred.

### 8. Ten hostile boundaries

All required fixtures are constructive and non-vacuous:

| Boundary | Exact receipt |
| --- | --- |
| R2 without uptake | `r2_without_uptake` |
| Availability without consumption | `availability_without_consumption`; stronger successful-presentation receipt `presented_availability_without_faithful_consumption` |
| Consumption without de-se dependence | `faithful_forecast_consumption_still_not_de_se_uptake` |
| De-se dependence without success | `de_se_dependence_without_success` |
| Successful output without uptake | `successful_output_without_uptake` |
| Records without uptake | `mnemonic_records_without_uptake` |
| Forecast grounding without uptake | `forecast_grounding_without_uptake` |
| R1 without uptake | `r1_without_uptake` |
| Two lawful R2 inputs with distinct consequences | `two_r2_inputs_each_have_r3_and_distinct_results` |
| Distinct R2 inputs with the same output | `distinct_r2_inputs_same_output_without_r3` |

Availability is not tested by removing the evaluator: the stronger fixture
successfully presents an independently lawful alternate but not the exact
input.  Forecast-only consumption faithfully presents the input and evaluates
its retained forecast, yet constructively factors through de-se erasure.

### 9. Remoding and provenance

`functional_uptake_remode` quantifies over an arbitrary replacement mode and
constructively transports and reflects inputs, lawfulness, presentation, and
evaluation.  The final theorem is axiom-free.  `traceValid` remains outside
the input, layer, and R3.  Valid mnemonic records remain insufficient for R3,
and no stronger provenance or causal claim is made.

### 10. Isomorphism and transport

The input isomorphism is derived from the frozen reference and forecast
isomorphisms and preserves/reflection-connects node realization, erasure, and
lawfulness.  `UptakeLayerIso` adds only an output isomorphism and commutation of
presentation and evaluation; it contains no R3 field.

Reverse R3 transport uses explicit input `invFun`/`right_inv`, phase-two R2
reflection, reference/forecast/output injectivity, and presentation/evaluation
commutation.  It assumes no unstated surjectivity, choice, proof irrelevance,
or equality reflection.  Rich witness transport follows through the
substantive characterization.

### 11. Constructivity and reproduction

Independent source search found no `sorry`, `admit`, custom axiom,
`Classical`, `choice`, `Quot`, `native_decide`, unsafe or partial declaration,
Mathlib import, external dependency, or hidden primitive use/dependence label.

The exact reproduction results were:

```text
lake env lean StaticRole/Campaign/PhaseThreeQualification.lean
exit 0; exactly 32 phase-three declarations printed axiom-free

lake build StaticRole
exit 0; Build completed successfully (30 jobs)

lake build CalculiStable CalculiScratch CalculiAll Calculi
exit 0; Build completed successfully (269 jobs)

python3 scripts/formalization_audit.py check --skip-external --skip-footprints
exit 0; FORMALIZATION AUDIT: PASS (19 checks)

git diff --check
exit 0; no output

git diff --check HEAD^ HEAD
exit 0; no output
```

Axiom result:

```text
32 / 32 axiom-free
0 propext
0 Quot.sound
0 Classical.choice
0 other axioms
```

## Residual limitations and exact claim

R3 is an existential, bounded discrimination result at one source, target, and
forecast context.  It does not claim universal usefulness, evaluator
correctness, or that every reference-sensitive refusal is uptake.  The
`currentReference` section remains explicit model structure.  Finite Bool and
three-center fixtures witness strictness; the definitions and transport laws
are carrier-polymorphic.

The ratified claim is:

> This formalization distinguishes external center-relative temporal roles,
> internal cross-center role encoding, coherence-grounded prospective de se
> representation, and structural functional uptake of that representation.

It does not establish temporal passage, phenomenal experience, consciousness,
awareness, qualia, metaphysical personal identity, rationality, successful
prediction, successful agency, psychology, neural implementation, or
predictive-processing theory.

No push, merge to `main`, tag, mint, publication, release, or external upload
is performed by this ratification.
