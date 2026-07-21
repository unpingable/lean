# Declaration crosswalk

This index maps the principal declarations used by the books to their exact
source locations and roles. The final column is repository metadata, not a
mathematical classification:

- **stable public surface** means the declaration is in the registered
  calculus root;
- **stable multi-root support** means a public supporting declaration is shared
  by more than one registered root;
- **supporting machinery** means a public helper outside the principal API;
- **retained adverse evidence** and **deferred predecessor** are not public Lean
  doctrine.

“Meta” identifies a repository record rather than an object-level Lean
declaration. No row implies runtime conformance.

## Governed-family core

| Declaration | Source | Mathematical role | Prerequisites | Consequence | Class |
|---|---|---|---|---|---|
| `Admissibility.Calculus.GovernedFamily` | [Core.lean:77](../../LeanProofs/Admissibility/Calculus/Core.lean#L77) | Common dependent signature | none | fixes claims, evidence, books, laws, total decision | stable public surface |
| `GovernedFamily.Authority` | [Core.lean:110](../../LeanProofs/Admissibility/Calculus/Core.lean#L110) | Derived judgment | family, claim | authority is exactly nonempty witness | stable public surface |
| `refusal_refutes_authority` | [Core.lean:113](../../LeanProofs/Admissibility/Calculus/Core.lean#L113) | Negative theorem | exclusivity, refusal | no authority for the same claim | stable public surface |
| `authority_requires_standing` | [Core.lean:120](../../LeanProofs/Admissibility/Calculus/Core.lean#L120) | Book projection | witness-to-standing law | authority entails standing | stable public surface |
| `authority_preserves_custody` | [Core.lean:125](../../LeanProofs/Admissibility/Calculus/Core.lean#L125) | Book projection | witness-to-custody law | authority entails custody | stable public surface |
| `authority_has_no_multiplicity` | [Core.lean:133](../../LeanProofs/Admissibility/Calculus/Core.lean#L133) | Squashing boundary | `Authority = Nonempty Witness` | authority proofs cannot count witnesses | stable public surface |
| `authority_iff_decide_isLeft` | [Core.lean:139](../../LeanProofs/Admissibility/Calculus/Core.lean#L139) | Checker coherence | total decision, exclusivity | Boolean branch view agrees with authority | stable public surface |
| `no_claim_erasing_check_is_faithful` | [Core.lean:159](../../LeanProofs/Admissibility/Calculus/Core.lean#L159) | Erasure countertheorem | collapsed witnessed/refused pair | no faithful Boolean check through that projection | stable public surface |

## Verdict, domain, and location substrate

| Declaration | Source | Mathematical role | Prerequisites | Consequence | Class |
|---|---|---|---|---|---|
| `CoreObstruction` | [Core.lean:74](../../LeanProofs/Admissibility/PathVerdict/Core.lean#L74) | Shared obstruction vocabulary | none | fixed core doctrine | stable multi-root support |
| `ObstructionKind` | [Core.lean:85](../../LeanProofs/Admissibility/PathVerdict/Core.lean#L85) | Core/domain sum | core, domain `δ` | distinguishes shared and native faults | stable multi-root support |
| `PathVerdict` | [Core.lean:96](../../LeanProofs/Admissibility/PathVerdict/Core.lean#L96) | Ordered diagnostic artifact | obstruction vocabulary | list-valued verdict | stable multi-root support |
| `PathVerdict.compose` | [Core.lean:105](../../LeanProofs/Admissibility/PathVerdict/Core.lean#L105) | Composition | two verdicts | ordered log append | stable multi-root support |
| `PathVerdict.AuthorityBearing` | [Core.lean:111](../../LeanProofs/Admissibility/PathVerdict/Core.lean#L111) | Verdict judgment | verdict | authority-bearing iff empty log | stable multi-root support |
| `authority_compose_iff` | [Core.lean:144](../../LeanProofs/Admissibility/PathVerdict/Core.lean#L144) | Composition seal | append semantics | composite clean iff both clean | stable multi-root support |
| `obstruction_blocks_authority` | [Core.lean:165](../../LeanProofs/Admissibility/PathVerdict/Core.lean#L165) | No-laundering theorem | logged obstruction | refutes authority-bearing | stable multi-root support |
| `PathVerdict.mapDomain` | [Domains.lean:127](../../LeanProofs/Admissibility/PathVerdict/Domains.lean#L127) | Vocabulary transport | total `δ → δ'` | renames every domain log entry | stable multi-root support |
| `fold_mapDomain` | [Domains.lean:223](../../LeanProofs/Admissibility/PathVerdict/Domains.lean#L223) | Naturality | edge map and fold | mapping commutes with folding | stable multi-root support |
| `mapDomain_authority_iff` | [Domains.lean:248](../../LeanProofs/Admissibility/PathVerdict/Domains.lean#L248) | Transport seal | total domain map | preserves and reflects emptiness | stable multi-root support |
| `core_mem_mapDomain_iff` | [Domains.lean:263](../../LeanProofs/Admissibility/PathVerdict/Domains.lean#L263) | Core preservation | domain map | exact core membership both ways | stable multi-root support |
| `domain_mem_mapDomain_iff` | [Domains.lean:282](../../LeanProofs/Admissibility/PathVerdict/Domains.lean#L282) | Native identity preservation | injective domain map | exact native membership both ways | stable multi-root support |
| `mixed_compose_authority_iff` | [Domains.lean:377](../../LeanProofs/Admissibility/PathVerdict/Domains.lean#L377) | Mixed-domain seal | sum injections | mixed path clean iff both pieces clean | stable multi-root support |
| `LabeledEdge` | [Located.lean:108](../../LeanProofs/Admissibility/PathVerdict/Located.lean#L108) | Carried input identity | identifier and edge verdict | binds label to edge | stable multi-root support |
| `LocatedVerdict` | [Located.lean:116](../../LeanProofs/Admissibility/PathVerdict/Located.lean#L116) | Located artifact | labels and obstruction vocabulary | log of label/fault pairs | stable multi-root support |
| `foldLocated` | [Located.lean:165](../../LeanProofs/Admissibility/PathVerdict/Located.lean#L165) | Sanctioned constructor | labeled edge list | located diagnostic fold | stable multi-root support |
| `forget_foldLocated` | [Located.lean:181](../../LeanProofs/Admissibility/PathVerdict/Located.lean#L181) | Erasure tether | sanctioned fold | exact unlocated fold after forgetting | stable multi-root support |
| `foldLocated_carries` | [Located.lean:233](../../LeanProofs/Admissibility/PathVerdict/Located.lean#L233) | Completeness | obstructed labeled edge | pair occurs in output | stable multi-root support |
| `foldLocated_sound` | [Located.lean:255](../../LeanProofs/Admissibility/PathVerdict/Located.lean#L255) | Soundness | logged pair from fold | matching input edge exists | stable multi-root support |
| `LocatedVerdict.mapId` | [Located.lean:306](../../LeanProofs/Admissibility/PathVerdict/Located.lean#L306) | Label transport | `ι → ι'` | relabels without changing faults | supporting machinery |

## Refusal spine

| Declaration | Source | Mathematical role | Prerequisites | Consequence | Class |
|---|---|---|---|---|---|
| `RefusalPacket` | [Spine.lean:61](../../LeanProofs/Admissibility/Calculus/Spine.lean#L61) | Dependent negative artifact | governed family | retains claim and its refusal | stable public surface |
| `SpineEncoding` | [Spine.lean:69](../../LeanProofs/Admissibility/Calculus/Spine.lean#L69) | Permissive refusal map | family | chooses `δ` and encoder | stable public surface |
| `SpineEncoding.funnel` | [Spine.lean:80](../../LeanProofs/Admissibility/Calculus/Spine.lean#L80) | Decision projection | family checker, encoder | clean or singleton refusal verdict | stable public surface |
| `funnel_decision_branches_ne` | [Spine.lean:107](../../LeanProofs/Admissibility/Calculus/Spine.lean#L107) | Branch separation | accepted and refused decisions | projected verdicts differ | stable public surface |
| `funnel_authority_iff` | [Spine.lean:119](../../LeanProofs/Admissibility/Calculus/Spine.lean#L119) | Judgment exactness | native decision | verdict and family authority agree | stable public surface |
| `LosslessEncoding` | [Spine.lean:174](../../LeanProofs/Admissibility/Calculus/Spine.lean#L174) | Exact refusal contract | spine encoding | decoder with both inverse laws | stable public surface |
| `decode_some_iff` | [Spine.lean:198](../../LeanProofs/Admissibility/Calculus/Spine.lean#L198) | Image exactness | both inverse laws | successful decode iff canonical encoding | stable public surface |
| `encodePacket_injective` | [Spine.lean:222](../../LeanProofs/Admissibility/Calculus/Spine.lean#L222) | Representation separation | decode/encode recovery | packet encoding injective | stable public surface |
| `no_subsingleton_domain_of_distinct_refusals` | [Spine.lean:238](../../LeanProofs/Admissibility/Calculus/Spine.lean#L238) | Collapse countertheorem | two distinct refusals | exact domain cannot be subsingleton | stable public surface |
| `refusal_recoverable` | [Spine.lean:247](../../LeanProofs/Admissibility/Calculus/Spine.lean#L247) | End-to-end refusal recovery | refusing native decision | funnel log recovers full packet | stable public surface |
| constant-`Unit` collapse | [admission ledger](../V14-READINESS-LEDGER.md#rung-4--the-exact-refusal-packet-spine-admitted-2026-07-18) | Adverse control for superseded contract | private counterexample | shows reason-only collapse | retained adverse evidence, not public Lean |

## Comparison framework

| Declaration | Source | Mathematical role | Prerequisites | Consequence | Class |
|---|---|---|---|---|---|
| `EntryIndex` | [Comparison.lean:68](../../LeanProofs/Admissibility/Calculus/Comparison.lean#L68) | Closed constitutional index | none | exactly seven named slots | stable public surface |
| `NativeDecisionTriple` | [Comparison.lean:152](../../LeanProofs/Admissibility/Calculus/Comparison.lean#L152) | Indexed source shape | none | claim/witness/refusal triple | stable public surface |
| `NativeSourceShape` | [Comparison.lean:160](../../LeanProofs/Admissibility/Calculus/Comparison.lean#L160) | Source classification | triple or gap | forces indexed shape or reason | stable public surface |
| `JudgmentView` | [Comparison.lean:168](../../LeanProofs/Admissibility/Calculus/Comparison.lean#L168) | Comparison observation | carrier and predicate | avoids invented native evidence | stable public surface |
| `Projection` | [Comparison.lean:175](../../LeanProofs/Admissibility/Calculus/Comparison.lean#L175) | Single declared map | source/target views | binds every receipt to one map | stable public surface |
| `ExactJudgmentReceipt` | [Comparison.lean:198](../../LeanProofs/Admissibility/Calculus/Comparison.lean#L198) | Judgment equivalence | projection | preservation and reflection | stable public surface |
| `ExactRepresentationReceipt` | [Comparison.lean:206](../../LeanProofs/Admissibility/Calculus/Comparison.lean#L206) | Recoverable exactness | exact judgment | canonical partial inverse | stable public surface |
| `DirectionalWithLossReceipt` | [Comparison.lean:216](../../LeanProofs/Admissibility/Calculus/Comparison.lean#L216) | Strict lossy comparison | projection | preservation plus collapsed pair | stable public surface |
| `SeparationReceipt` | [Comparison.lean:231](../../LeanProofs/Admissibility/Calculus/Comparison.lean#L231) | Non-subsumption evidence | source and target controls | source-positive image refused | stable public surface |
| `ComparisonLaw` | [Comparison.lean:240](../../LeanProofs/Admissibility/Calculus/Comparison.lean#L240) | Dependent law selection | kind and projection | label requires matching proof | stable public surface |
| `ExactRepresentationReceipt.map_injective` | [Comparison.lean:269](../../LeanProofs/Admissibility/Calculus/Comparison.lean#L269) | Derived exactness | exact representation receipt | map injective | stable public surface |
| `DirectionalWithLossReceipt.no_left_inverse` | [Comparison.lean:295](../../LeanProofs/Admissibility/Calculus/Comparison.lean#L295) | Loss theorem | collapsed pair | no total source recovery | stable public surface |
| `CapabilityDisposition` | [Comparison.lean:338](../../LeanProofs/Admissibility/Calculus/Comparison.lean#L338) | Proof-bearing support | receipt proposition | support or classified obstruction | stable public surface |
| `IndexedEntry` | [Comparison.lean:410](../../LeanProofs/Admissibility/Calculus/Comparison.lean#L410) | Proof-carrying table row | pins, projection, law, capabilities | one complete indexed comparison | stable public surface |
| `Ledger` | [Comparison.lean:424](../../LeanProofs/Admissibility/Calculus/Comparison.lean#L424) | Exhaustive table shape | indexed entries | entry for every constructor | stable public surface |
| concrete seven-entry ledger | [admission boundary](../V14-READINESS-LEDGER.md#rung-5--the-indexed-comparison-framework-admitted-2026-07-18) | Reviewed realization | private adapters and pins | evidence for framework inhabitation | supporting evidence, not public Lean |

## Stored-decision crossing

| Declaration | Source | Mathematical role | Prerequisites | Consequence | Class |
|---|---|---|---|---|---|
| `Crossing.Spec` | [Crossing.lean:59](../../LeanProofs/Admissibility/Calculus/Crossing.lean#L59) | Binary crossing input | two families and lossless spines | fixes crossing pair | stable public surface |
| `Crossing.Refusal` | [Crossing.lean:77](../../LeanProofs/Admissibility/Calculus/Crossing.lean#L77) | Evidence-preserving negative sum | paired claim | retains mixed witness or both refusals | stable public surface |
| `NativeDecisions` | [Crossing.lean:93](../../LeanProofs/Admissibility/Calculus/Crossing.lean#L93) | Stored native results | paired claim | retains both `Sum` values | stable public surface |
| `check` | [Crossing.lean:103](../../LeanProofs/Admissibility/Calculus/Crossing.lean#L103) | Sole evaluation boundary | crossing spec and claim | calls each native decision once | stable public surface |
| `CheckedCrossing.result` | [Crossing.lean:109](../../LeanProofs/Admissibility/Calculus/Crossing.lean#L109) | Pure stored fold | native decisions | composite witness/refusal | stable public surface |
| `CheckedCrossing.verdict` | [Crossing.lean:129](../../LeanProofs/Admissibility/Calculus/Crossing.lean#L129) | Pure diagnostic projection | stored result | mixed-domain verdict | stable public surface |
| `CheckedCrossing.located` | [Crossing.lean:142](../../LeanProofs/Admissibility/Calculus/Crossing.lean#L142) | Pure located projection | stored result | left/right diagnostic | stable public surface |
| `authority_iff_components` | [Crossing.lean:180](../../LeanProofs/Admissibility/Calculus/Crossing.lean#L180) | Binary authority law | paired witness definition | authority iff both native authorities | stable public surface |
| `both_refusals_located_and_decode` | [Crossing.lean:342](../../LeanProofs/Admissibility/Calculus/Crossing.lean#L342) | Non-shadowing theorem | stored double refusal, exact spines | both ordered faults exactly recover | stable public surface |
| `CheckedPacket` | [Crossing.lean:366](../../LeanProofs/Admissibility/Calculus/Crossing.lean#L366) | Stored comparison carrier | claim and checked result | freezes observed evaluation | stable public surface |
| `checkedProjectionExact` | [Crossing.lean:393](../../LeanProofs/Admissibility/Calculus/Crossing.lean#L393) | Stored judgment receipt | checked packet | authority agrees with stored branch | stable public surface |

## Concrete families and boundaries

| Declaration | Source | Mathematical role | Prerequisites | Consequence | Class |
|---|---|---|---|---|---|
| `Weathering.Admissible` | [Native.lean:74](../../LeanProofs/Admissibility/Calculus/Instances/Weathering/Native.lean#L74) | Static native judgment | weather and disposition | licenses a reliance mode | stable public surface |
| `Weathering.weathering` | [Weathering.lean:48](../../LeanProofs/Admissibility/Calculus/Instances/Weathering.lean#L48) | Governed adapter | native Weathering | total family with empty obligation | stable public surface |
| `weathering_authority_iff_native` | [Weathering.lean:80](../../LeanProofs/Admissibility/Calculus/Instances/Weathering.lean#L80) | No-distortion theorem | adapter | authority iff native admissibility | stable public surface |
| `PaidClaim` | [BoundedPaidReachability.lean:87](../../LeanProofs/Admissibility/Calculus/Instances/BoundedPaidReachability.lean#L87) | Bounded claim index | fixed fixtures | retains funded/bare origin | stable public surface |
| `Barrier` | [BoundedPaidReachability.lean:101](../../LeanProofs/Admissibility/Calculus/Instances/BoundedPaidReachability.lean#L101) | Dynamic refusal certificate | origin and fixed goal | forward-closed exclusion | stable public surface |
| `boundedPaidReachability` | [BoundedPaidReachability.lean:130](../../LeanProofs/Admissibility/Calculus/Instances/BoundedPaidReachability.lean#L130) | Governed adapter | two fixtures and run substrate | fixed total decision | stable public surface |
| `signature_refuses_endpoint_only_checks` | [BoundedPaidReachability.lean:190](../../LeanProofs/Admissibility/Calculus/Instances/BoundedPaidReachability.lean#L190) | Concrete erasure theorem | same endpoint, opposed claims | no endpoint-only faithful checker | stable public surface |
| `green_gate_cannot_cure_unfunded_passage` | [crossing leaf:128](../../LeanProofs/Admissibility/Calculus/Instances/WeatheringBoundedPaidCrossing.lean#L128) | Mixed negative theorem | fresh gate, bare passage | crossing lacks authority | stable public surface |
| `stale_bare_double_fault_nonshadowing` | [crossing leaf:204](../../LeanProofs/Admissibility/Calculus/Instances/WeatheringBoundedPaidCrossing.lean#L204) | Double-fault control | stale and bare fixture | both exact refusals retained | stable public surface |
| `LifecycleOrigin` | [LifecycleOrigin.lean:41](../../LeanProofs/Admissibility/Calculus/Instances/BreakGlass/LifecycleOrigin.lean#L41) | Origin namespace | domain, epoch, nonce | qualifies all native references | stable public surface |
| `BreakGlass.Claim` | [BreakGlass.lean:62](../../LeanProofs/Admissibility/Calculus/Instances/BreakGlass.lean#L62) | Origin-bearing phase claim | lifecycle origin and phase | prevents phase-only identity | stable public surface |
| `BreakGlass.Refusal` | [BreakGlass.lean:142](../../LeanProofs/Admissibility/Calculus/Instances/BreakGlass.lean#L142) | Structured refusal family | atoms and claim | foreign/ordinary/audit cases | stable public surface |
| `BreakGlass.Standing` | [BreakGlass.lean:169](../../LeanProofs/Admissibility/Calculus/Instances/BreakGlass.lean#L169) | Family-native standing book | phase ledgers and receipts | phase-specific basis | stable public surface |
| `BreakGlass.Custody` | [BreakGlass.lean:185](../../LeanProofs/Admissibility/Calculus/Instances/BreakGlass.lean#L185) | Family-native custody book | phase ledgers | phase-specific provenance | stable public surface |
| `BreakGlass.Obligation` | [BreakGlass.lean:204](../../LeanProofs/Admissibility/Calculus/Instances/BreakGlass.lean#L204) | Family-native obligation book | exact origin-qualified ref | exact live-obligation query | stable public surface |
| `BreakGlass.governedFamily` | [BreakGlass.lean:210](../../LeanProofs/Admissibility/Calculus/Instances/BreakGlass.lean#L210) | Terminal governed instance | supplied `Atoms` and native lifecycle | six-phase total checker | stable public surface |
| `commit_opens_exact_obligation` | [BreakGlass.lean:316](../../LeanProofs/Admissibility/Calculus/Instances/BreakGlass.lean#L316) | Lifecycle theorem | native commit | exact obligation becomes live | stable public surface |
| `settlement_closes_exact_obligation` | [BreakGlass.lean:320](../../LeanProofs/Admissibility/Calculus/Instances/BreakGlass.lean#L320) | Lifecycle theorem | native settlement | exact obligation no longer live | stable public surface |
| `authority_retains_claim_origin` | [BreakGlass.lean:410](../../LeanProofs/Admissibility/Calculus/Instances/BreakGlass.lean#L410) | Origin preservation | family authority | claim origin equals target origin | stable public surface |
| `phase_only_checker_cannot_be_faithful` | [BreakGlass.lean:427](../../LeanProofs/Admissibility/Calculus/Instances/BreakGlass.lean#L427) | Concrete erasure theorem | foreign twin at same phase | no faithful phase-only checker | stable public surface |
| `exceptionalOrdinaryVerdictSeparation` | [Comparison.lean:68](../../LeanProofs/Admissibility/Calculus/Instances/BreakGlass/Comparison.lean#L68) | Bounded C1 separation | supplied atoms and retained verdict | exceptional authority fails ordinary target | stable public surface |
| historical `AuthorizedStep` crossing | [boundary:79](../../LeanProofs/Admissibility/Calculus/Instances/BreakGlass/Comparison.lean#L79) | Stronger predecessor claim | independently native model lacks target bridge | neither proved nor refuted here | deferred/adverse predecessor |
| `weatheringBreakGlass` | [Crossing.lean:56](../../LeanProofs/Admissibility/Calculus/Instances/BreakGlass/Crossing.lean#L56) | Terminal crossing specification | weather and BreakGlass exact spines | binary stored crossing | stable public surface |
| `foreign_crossing_location_decodes_exactly` | [Crossing.lean:165](../../LeanProofs/Admissibility/Calculus/Instances/BreakGlass/Crossing.lean#L165) | Origin/refusal preservation | foreign claim | right location and full packet recover | stable public surface |

## Coverage accounting

The books directly crosswalk 90 principal declarations or boundary
records above. The stable proof gates cover a larger theorem inventory:

| Frozen inventory | Count | Authority |
|---|---:|---|
| `PathVerdict` substrate receipts | 36 | [`check-pathverdict-footprint.sh`](../../scripts/check-pathverdict-footprint.sh) |
| calculus-root receipts | 191 | [`check-calculus-footprint.sh`](../../scripts/check-calculus-footprint.sh) |
| total theorem receipts in the calculus closure | 227 | sum of the disjoint gate inventories |

The 90-row conceptual crosswalk is not a substitute for the theorem-by-theorem
axiom manifests in those gates. It indexes every definition and theorem on
which the exposition's major claims depend; specialized BreakGlass lifecycle
receipts are grouped under the instance and its exact gate.
