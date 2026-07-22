# StaticRole phase-three qualification

**Fast-falsification result:** `FUNCTIONAL-UPTAKE-SPECIMEN-SUPPORTED`

**Candidate verdict:** `READY-FOR-PHASE-THREE-OPERATOR-RATIFICATION`

Phase three earns a bounded structural distinction between possessing a
coherence-grounded prospective de se representation and using it in a
downstream transition.  R3 requires faithful presentation of the canonical
transported-reference input and a constructive same-context discrimination:
another lawful input with the same forecast context but a different reference
coordinate produces a different output.  No field asserts use, relevance,
dependence, success, behavior, awareness, or agency.

## Authoritative baseline and entry state

The campaign began on branch `gt3-stage3-candidate-h11` at the exact ratified
phase-two revision:

```text
phase-two candidate:           0a203e95ddf7f96f9f71a8e9d8b4b60bbde8a349
phase-two candidate tree:      5e30ce0d96e058063741df5665070fbb37c61887
phase-two candidate parent:    421d5cdb0b14a40c81711ce137a4b47842d8ed39
phase-two ratification:        63d54e777e2670866806e1a7ee30798e55f3aae9
phase-two ratification tree:   e7561908482446f8414a29a823cd4b787bccbdcc
ratification parent/candidate: 0a203e95ddf7f96f9f71a8e9d8b4b60bbde8a349
```

All pins and parent relations were verified before mutation.  The scoped
formalization worktree had no tracked or staged change.  Pre-existing untracked
sibling work under `../nq-ng/` and `../ux-design/` was recorded and left
untouched.  Neither phase-two commit was amended, squashed, rebased, or
rewritten, and no phase-two source or ratification record changed.

## Additive phase-three surface

| Module | Bounded responsibility |
| --- | --- |
| `Functional.Uptake` | typed prospective input, stored R2 receipt, presentation interface, faithful consumption, remoding |
| `Functional.Dependence` | R3, concrete node-level witness, characterization, run discrimination, non-factorization |
| `Countermodels.UptakeHostiles` | finite same-reduct pair, ten required hostile boundaries, three-center optional fixture |
| `Theorems.UptakeIndependence` | named hierarchy, correctness, and same-reduct results |
| `Model.UptakeIsomorphism` | derived input isomorphism and functional-layer isomorphism |
| `Model.UptakeTransport` | constructive preservation and reflection of R3 and its rich witness |
| `Campaign.PhaseThreeQualification` | isolated phase-three closure and 32 direct axiom audits |

`StaticRole.lean` now imports the additive phase-three qualification leaf.
The `StaticRole` Lake library remains non-default and remains absent from the
`Calculi`, `CalculiAll`, `CalculiStable`, custody, and release aggregates.

## Minimal functional signature

`ProspectiveFunctionalInput F c d` has only two data fields:

```lean
reference : F.Reference
forecast  : I.ForecastToken
```

The source and prospective target are type indices.  The represented node,
host stage, target, perspective, and current role are derived from the frozen
phase-two frame, so a second node description cannot diverge from the reference
coordinate.  `eraseDeSe` removes exactly the reference and retains the forecast.

`LawfulProspectiveInput` requires exact forecast hosting at `c,d` and grounding
of the frame-realized node.  `AvailableProspectiveEncoding` is deliberately a
Type-valued stored R2 receipt, not downstream availability; its `Nonempty`
existence is equivalent to R2.  Interface availability is instead
`PresentedInputAvailable`, and faithful consumption is the stronger equation
`present input = some input`.

`UptakeLayer F A` contains:

```lean
Output  : Type
present : (c d) -> ProspectiveFunctionalInput F c d ->
            Option (ProspectiveFunctionalInput F c d)
evaluate : (c d) -> ProspectiveFunctionalInput F c d -> Output
```

Presentation must preserve forecast erasure and lawfulness.  There is no
primitive `usedForPrediction`, `usedForAction`, `functionallyActive`,
`influencesBehavior`, `uptakeOccurred`, `usesDeSe`, or `dependsOnDeSe` field.

## Exact R3 definition

The implemented predicate is:

```lean
def FunctionalUptake
    {B : StaticBase} {I : InformationLayer B}
    {R : RepresentationLayer I}
    (F : SelfReferenceFrame R)
    (A : CoherentReferenceAction F)
    (U : UptakeLayer F A)
    (c d : B.Center) : Prop :=
  ProspectiveDeSeEncoding F A c d ∧
  ∃ actual alternate : ProspectiveFunctionalInput F c d,
    LawfulProspectiveInput F c d actual ∧
    LawfulProspectiveInput F c d alternate ∧
    actual.reference = A.carry c d (F.currentReference c) ∧
    actual.eraseDeSe = alternate.eraseDeSe ∧
    actual.reference ≠ alternate.reference ∧
    U.present c d actual = some actual ∧
    U.present c d alternate = some alternate ∧
    U.evaluate c d actual ≠ U.evaluate c d alternate
```

R3 therefore contains R2, exact lawful consumption, and a concrete
counterfactual discrimination at one fixed source, target, and forecast
context.  Since the two inputs share the only non-de-se computational field,
their output difference is forced to track the reference coordinate.  Merely
passing an ignored argument, producing an output, or returning the correct
answer does not establish R3.

The five conceptual levels remain separate:

| Level | Exact phase-three witness |
| --- | --- |
| Possession | `Nonempty AvailableProspectiveEncoding`, equivalent to R2 |
| Availability | `PresentedInputAvailable`, an inhabited successful presentation |
| Consumption | `FaithfullyConsumes`, exact self-presentation |
| Dependence | same-erasure reference discrimination with unequal outputs |
| Success | separate model-local `OutputCorrect`; absent from R3 |

## Characterization and load-bearing law

`CoherentFunctionalUptakeWitness` records a stored R2 receipt, lawful actual and
alternate inputs, their concrete realized nodes and erasures, successful
presentations, and unequal observed evaluator outputs.  It does not contain a
`FunctionalUptake` or free dependence field.

The central theorem is:

```lean
functional_uptake_iff_nontrivial_de_se_dependence :
  FunctionalUptake F A U c d ↔
    Nonempty (CoherentFunctionalUptakeWitness F A U c d)
```

The forward proof constructs the node-level receipt.  The reverse proof uses
`referenceNode_injective` twice in a load-bearing way: first to recover the
canonical carried reference from the actual endpoint equality, and then to
recover exact supplied-input identity from presentation-node equality.
Forecast-erasure equality supplies the remaining input coordinate.  Without
frame injectivity, distinct references may realize one node and neither
recovery is available; the reverse direction does not go through unchanged.

`functional_uptake_run_discrimination` lifts raw evaluator inequality to
observable `run` inequality.  `functional_uptake_not_factors_through_erasure`
constructively proves that an R3 transition cannot factor through the retained
forecast alone.  It introduces no function extensionality or classical
non-factorization principle.

## Critical same-reduct gate

The central pair reuses the literal phase-two objects:

* `coherenceBase`;
* `coherenceInformation`;
* `coherenceRepresentation`;
* `coherenceFrame`;
* `parityAction`;
* one R2 receipt, its lawful actual and alternate inputs, output carrier, and
  reference-sensitive evaluator.

`faithfulUptake` presents each lawful input unchanged.  `neutralizingUptake`
presents either input as the independently lawful and forecast-grounded
`false` reference in the same target fiber.  That alternate is not a failure
sentinel.  The two layers differ only in this lawful presentation wiring; the
theorem `central_presentations_share_output_and_evaluator` proves their output
carrier and evaluator are literal matches.

Consequently:

```text
faithful presentation:    R3
neutralizing presentation: not R3, factors through de-se erasure
```

The disagreement is not an asserted Boolean and does not come from swapping
arbitrary evaluators.

The optional three-center fixture adds two actual R2 inputs in one shared base,
information layer, representation layer, frame, action, and evaluator.  The
reference-sensitive evaluator gives both inputs R3 and distinct results.  A
constant evaluator over that same frame/action gives the two R2 inputs the same
result and gives neither R3.  The unused off-path role cells are arbitrary but
no theorem relies on them; both exact source-to-target R1 atlases are proved.

## Hostile fixture ledger

| # | Required boundary | Constructive receipt |
| ---: | --- | --- |
| 1 | R2 without uptake | `r2_without_uptake` |
| 2 | availability without consumption | `availability_without_consumption`; `presented_availability_without_faithful_consumption` |
| 3 | consumption of non-de-se data | `faithful_forecast_consumption_still_not_de_se_uptake` |
| 4 | de-se dependence without success | `de_se_dependence_without_success` |
| 5 | successful output without uptake | `successful_output_without_uptake` |
| 6 | mnemonic records without uptake | `mnemonic_records_without_uptake` |
| 7 | forecast grounding without uptake | `forecast_grounding_without_uptake` |
| 8 | R1 without uptake | `r1_without_uptake` |
| 9 | two lawful R2 inputs, distinct consequences | `two_r2_inputs_each_have_r3_and_distinct_results` |
| 10 | distinct R2 inputs, same functional output | `distinct_r2_inputs_same_output_without_r3` |

Additional receipts cover refusal before evaluation, continuation without
uptake, constant factorization, and forecast-only factorization.  Every hostile
is inhabited in its neighboring structure and fails constructively rather than
through an empty premise.

## Correctness independence

One shared criterion is used in both directions:

```lean
def OutputCorrect (output : Bool) : Prop := output = false
```

The faithful R3 transition returns `true`, so R3 does not imply correctness.
The constant input-insensitive transition returns the correct `false`, so
correctness does not imply R3.  Correctness is not a field of `UptakeLayer` or
`FunctionalUptake`.

## Annotation and provenance decisions

`functional_uptake_remode` proves preservation and reflection under arbitrary
replacement of annotation-only `mode`.  Its constructive proof transports the
input and presentation equations explicitly.  A preliminary proof inherited
`propext` through broad simplification; qualification rejected that proof and
replaced it with direct Option and input equalities.  The final remoding
definition, helper theorems, and R3 invariance are axiom-free.

`traceValid` remains outside R3.  The mnemonic hostile retains valid records
yet has no R3, which is the honest smaller result.  Phase three does not claim
that provenance is functionally integrated, nor that invalid provenance is
irrelevant to every possible downstream interface.

## Full isomorphism and transport

`prospectiveFunctionalInputIso` derives the input isomorphism from the frozen
phase-two reference and forecast isomorphisms.  Node realization, erasure, and
input lawfulness are preserved and reflected.

`UptakeLayerIso` adds only:

* an explicit output isomorphism;
* commutation of `present` with the derived input isomorphism;
* commutation of `evaluate` with the input and output isomorphisms.

It contains no R3 field.  `functional_uptake_transport` preserves and reflects
R3 constructively.  The reverse direction uses the explicit input/output
inverses and injectivity already present in the isomorphisms; it assumes no
surjectivity beyond that data and uses no choice.  The rich witness transports
through the substantive characterization.  Frozen phase-two transport results
are unchanged.

## Constructivity and axiom footprint

The phase-three qualification leaf directly audits 32 load-bearing new
declarations.  Result:

```text
32 / 32 axiom-free
0 propext
0 Quot.sound
0 Classical.choice
0 other axioms
```

The imported frozen phase-two leaf remains its separately ratified 48/48
axiom-free object.  Source search over the complete phase-three surface found
no `sorry`, `admit`, custom `axiom`, `Classical`, `choice`, `Quot`,
`native_decide`, `unsafe`, `partial`, Mathlib import, external dependency, or
conclusion-equivalent use label.  The sole textual `axiom` match is the
qualification leaf's explanatory phrase `axiom-audit`.

## Verification receipts

The exact required commands completed successfully:

```text
lake env lean StaticRole/Campaign/PhaseThreeQualification.lean
exit 0; 32/32 phase-three declarations printed axiom-free

lake build StaticRole
exit 0; Build completed successfully (30 jobs)

lake build CalculiStable CalculiScratch CalculiAll Calculi
exit 0; Build completed successfully (269 jobs)

python3 scripts/formalization_audit.py check --skip-external --skip-footprints
exit 0; FORMALIZATION AUDIT: PASS (19 checks)

git diff --check
exit 0; no output
```

An independent hostile review found and caused repair of one real calibration
defect before qualification: the first draft used two different correctness
predicates for the two non-implications.  Both now use `OutputCorrect`.  A
second qualification defect, inherited `propext` in remoding proof automation,
was also removed before the final receipts above.  Neither repair changed the
R3 definition or the critical shared-reduct result.

## Exact line counts

```text
uptake signature and presentation:     438  StaticRole/Functional/Uptake.lean
dependence/coherence total:             290  StaticRole/Functional/Dependence.lean
  central characterization block:       73  lines 82-154 of Dependence.lean
hostile fixtures:                       590  StaticRole/Countermodels/UptakeHostiles.lean
named hierarchy/characterization API:  121  StaticRole/Theorems/UptakeIndependence.lean
transport:                              454  280 UptakeIsomorphism + 174 UptakeTransport
qualification leaf:                     45  StaticRole/Campaign/PhaseThreeQualification.lean
qualification documentation:           348  this record
aggregate root:                           6  StaticRole.lean
```

Counts use physical lines (`wc -l`).  The 73-line central block is included in
the 290-line dependence/coherence total and is shown separately because its
load-bearing reverse construction is a qualification gate.

## Remaining limitations and ratified boundary

R3 is existential and bounded: it witnesses discrimination between two lawful
inputs at one source/target/forecast context.  It does not claim that every use
of an R2 representation is discriminating, that an evaluator is globally
useful, or that the supplied `currentReference` section is semantically
adequate in general.  Presentation lawfulness is a general interface invariant;
the R3 branch uses the stronger exact self-presentation equations.  The
three-center optional fixture is finite and intentionally psychologically
neutral.

The exact claim proposed for ratification is:

> This specimen formalizes a bounded structural distinction between possessing
> a coherence-grounded prospective de se representation and functionally using
> it in a lawful transition whose result depends on its transported reference
> component.

It does not establish phenomenal temporal flow, subjective experience,
consciousness, awareness, qualia, metaphysical personal identity, unrestricted
agency, rationality, successful prediction, successful action, human
psychology, neural implementation, or predictive-processing theory.

The candidate commit and tree belong in the operator handoff because a commit
cannot contain its own identity.  No push, merge to `main`, tag, mint,
publication, release, or external upload is authorized or performed here.
