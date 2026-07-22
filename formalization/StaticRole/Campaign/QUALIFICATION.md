# StaticRole phase-two qualification

**Verdict:** `READY-FOR-OPERATOR-RATIFICATION`

The bounded repair passes the phase-two fast-falsification gate.  R2 no
longer reads a primitive selfhood label or epistemic mode.  Its decisive
condition is alignment of a designated current-reference section with a
globally lawful reference action satisfying identity, composition, and
continuation-to-node-order laws.  The critical finite pair shares one literal
base, information layer, representation layer, reference frame, role atlas,
forecast grounding, continuation relation, and current-reference section.
It differs only in two lawful total actions.

This remains a deliberately narrow result.  It establishes a structural
representational bridge, not the semantic adequacy of first-person reference
in general.

## Repository and phase-one baseline

- Repository: `/home/jbeck/git/skunkworks`
- Package directory: `/home/jbeck/git/skunkworks/formalization`
- Branch at phase-two entry: `gt3-stage3-candidate-h11`
- Entry `HEAD`: `421d5cdb0b14a40c81711ce137a4b47842d8ed39`
- Entry whole-repository tree:
  `7784d48b3682d63e182511bad4f131789af214a3`
- Entry `formalization` subtree:
  `08c814466ab4b304c936ea95be94251e2f8aa32d`
- Entry scoped status: modified `lakefile.toml`, untracked
  `StaticRole.lean`, and untracked `StaticRole/`.
- Unrelated pre-existing dirt: untracked sibling paths under `../nq-ng/`
  and `../ux-design/`.  None was modified or staged by this campaign.

The entry state was the complete, technically green phase-one specimen with
the recorded verdict `FORMAL-SPECIMEN-TOO-TRIVIAL`.  Before refactoring, its
file inventory and SHA-256 values, branch, commit, tree, status, build result,
and 21 empty axiom audits were recorded in the campaign working log.  The
phase-one R0/R1 core, dependency fixtures, accuracy separation, and original
qualification diagnosis were retained as the baseline.  The old R2 claims
whose truth depended on `isSelf` and `mode` were intentionally removed
rather than silently relabelled.

The candidate commit and tree are recorded in the operator handoff because a
commit cannot contain its own hash.  No push, tag, mint, publication, release,
or external upload was performed.

## Module and declaration inventory

| Module | Primary phase-two content |
| --- | --- |
| `StaticRole.Core.*` | `StaticBase`, `SameObserver`, `CenterBefore`, `ExternalRole`, R0 |
| `StaticRole.Information.*` | fixed stages, separate records/forecasts, provenance fields |
| `Representation.Layer` | representation nodes and relations; no `isSelf`; annotation-only `mode`; `remode` |
| `Representation.RoleEncoding` | `Encodes`, separate `AccurateEncoding`, R1 |
| `Representation.SelfReference` | `SelfReferenceFrame`, `CoherentReferenceAction`, derived anchor preservation and uniqueness laws |
| `Representation.DeSeProjection` | repaired R2, rich coherent witness, characterization, remoding invariance |
| `Model.Expansion` | literal-reduct `Expansion` and lawful `CoherentExpansion` |
| `Model.Isomorphism` | eight-sort `FullSignatureIso` |
| `Model.Transport` | constructive preservation/reflection for R0, R1, R2, anchors, preservation, and rich witnesses |
| `Countermodels.DependencyChain` | retained physical/information dependency fixtures |
| `Countermodels.RoleHierarchy` | retained R0/R1, self-anchor/R1, remoding, and accuracy controls |
| `Countermodels.Provenance` | Option B definitional nondependence receipt |
| `Countermodels.CoherenceHostiles` | central lawful-action pair and ten hostile phase-two separations |
| `Theorems.ExpansionIndependence` | named R0/R1/R2 existence and same-reduct results |
| `Campaign.Qualification` | isolated import and 48-theorem axiom audit |

`StaticRole.lean` remains the only package root.  The `StaticRole` Lake
target remains non-default and is absent from `Calculi`, `CalculiAll`,
`CalculiStable`, generated custody aggregates, and release metadata.

## Exact hierarchy

R0 is still derived solely from center equality, common ownership, and the
one physical causal relation:

```lean
def ExternalRoleShift (B : StaticBase) (c d : B.Center) : Prop :=
  SameObserver B c d ∧
  CenterBefore B c d ∧
  ExternalRole B c c .current ∧
  ExternalRole B c d .future ∧
  ExternalRole B d c .past ∧
  ExternalRole B d d .current
```

R1 remains a four-cell atlas hosted at the actual stage of `c`:

```lean
def InternalRoleEncoding
    {B : StaticBase} {I : InformationLayer B}
    (R : RepresentationLayer I) (c d : B.Center) : Prop :=
  ExternalRoleShift B c d ∧
  Encodes R c c c .current ∧
  Encodes R c c d .future ∧
  Encodes R c d c .past ∧
  Encodes R c d d .current
```

The new reference frame supplies a typed reference coordinate, its concrete
node realization at each host/represented-center pair, a unique designated
current coordinate at each center, injectivity, exact node coordinates and
role, and forecast-coordinate soundness:

```lean
structure SelfReferenceFrame (R : RepresentationLayer I) where
  Reference : Type uA
  referenceNode : B.Center → B.Center → Reference → R.RepNode
  currentReference : B.Center → Reference
  referenceNode_injective :
    ∀ host represented, Function.Injective (referenceNode host represented)
  nodeStage_reference :
    ∀ host represented ref,
      R.nodeStage (referenceNode host represented ref) = I.actualStage host
  perspective_reference :
    ∀ host represented ref,
      R.perspective (referenceNode host represented ref) = some represented
  target_reference :
    ∀ host represented ref,
      R.target (referenceNode host represented ref) = some represented
  role_reference :
    ∀ host represented ref,
      R.encodedRole (referenceNode host represented ref) = .current
  grounding_coordinates :
    ∀ host represented ref forecast,
      R.groundedByForecast (referenceNode host represented ref) forecast →
      ForecastHostedFor I forecast host represented
```

The action is total and globally coherent:

```lean
structure CoherentReferenceAction (F : SelfReferenceFrame R) where
  carry : B.Center → B.Center → F.Reference → F.Reference
  carry_refl :
    ∀ center ref, carry center center ref = ref
  carry_comp :
    ∀ a b c ref, carry b c (carry a b ref) = carry a c ref
  continuation_before :
    ∀ c d ref,
      R.continuationCandidate c d →
      R.repBefore
        (F.referenceNode c c ref)
        (F.referenceNode c d (carry c d ref))
```

The decisive bridge is derived, not stored:

```lean
def PreservesCurrentReference
    (F : SelfReferenceFrame R)
    (A : CoherentReferenceAction F)
    (c d : B.Center) : Prop :=
  A.carry c d (F.currentReference c) = F.currentReference d
```

R2 is exactly:

```lean
def ProspectiveDeSeEncoding
    (F : SelfReferenceFrame R)
    (A : CoherentReferenceAction F)
    (c d : B.Center) : Prop :=
  InternalRoleEncoding R c d ∧
  R.continuationCandidate c d ∧
  PreservesCurrentReference F A c d ∧
  ∃ forecast,
    ForecastHostedFor I forecast c d ∧
    R.groundedByForecast
      (F.referenceNode c d
        (A.carry c d (F.currentReference c)))
      forecast
```

`isSelf` was removed.  `CurrentSelfNode`, `ProjectedSelfNode`, and
`SelfLocated` are now derived from the injective frame realization and the
functional `currentReference` section.  `mode` remains only to retain
mnemonic metadata; `prospective_de_se_remode` proves that replacing every
mode cannot change R2.

## Coherence obligations and characterization

Identity and composition imply, constructively:

- round trip:
  `carry d c (carry c d ref) = ref`;
- injectivity of every `carry c d`;
- reflexive, compositional, and reverse preservation of the current section;
- uniqueness of canonical current and projected nodes;
- node-level represented succession for every declared continuation;
- coordinate-correct forecast grounding.

`CoherentProspectiveWitness` records explicit current/projected nodes, the
forecast, canonical endpoint equations, the carried-node endpoint equation,
continuation, `repBefore`, hosting and grounding, all node coordinates,
`AccurateEncoding`, and the forced round trip.

The central characterization is:

```lean
theorem prospective_de_se_iff_coherent_transport :
  ProspectiveDeSeEncoding F A c d ↔
    InternalRoleEncoding R c d ∧
    Nonempty (CoherentProspectiveWitness F A c d)
```

The forward proof constructs every receipt from R1 and the frame/action laws.
The reverse proof does not merely unfold R2: it combines the carried endpoint
with the projected-node equation and applies
`referenceNode_injective c d` to recover
`PreservesCurrentReference F A c d`.

Role accuracy remains separate from node presence.  R1's R0 conjunct upgrades
all four atlas cells through
`internal_role_encoding_has_accurate_atlas`.  The misrole hostile fixture
retains a lawful preserving action, continuation, and grounding but fails R2
because its future atlas cell is inaccurate.

## Critical literal-shared-reduct construction

The central definitions are `coherenceBase`, `coherenceInformation`,
`coherenceRepresentation`, and `coherenceFrame`.

- `Center := Bool`; the only causal edge is `false → true`.
- `RecordToken := Empty`; one `PUnit` forecast is hosted at `false` and
  targets `true`.
- The node carrier has four atlas nodes and reference nodes indexed by host,
  represented center, and `Bool` reference.
- The shared `repBefore` graph contains every edge between the two source
  and two destination reference coordinates.
- Both destination reference nodes are grounded by the same forecast.
- The shared continuation relation contains only `false → true`.
- `Reference := Bool` and `currentReference c := c`.

The two explicit `CoherentExpansion coherenceInformation` values reduce to
the same representation and frame terms:

```lean
parityCarry false true ref = flip ref
fixedCarry  false true ref = ref
```

Both are total actions satisfying identity, all eight center triples of
composition, constructive reversibility/injectivity, and continuation/order
compatibility.  The parity action maps the shared current coordinate
`false` to the destination current coordinate `true`; the fixed action
maps it to the alternate grounded coordinate `false`.

Thus:

```lean
same_reduct_lawful_actions_disagree_on_r2 :
  ProspectiveDeSeEncoding coherenceFrame parityAction false true ∧
  ¬ ProspectiveDeSeEncoding coherenceFrame fixedAction false true
```

The stronger
`same_reduct_lawful_actions_disagree_on_coherent_transport` proves the same
split for existence of the rich witness.  The negative theorem
`fixed_action_satisfies_all_neighboring_conditions` separately proves R1,
continuation, correct forecast hosting, and grounding of its actually carried
endpoint.  Its sole missing R2 conjunct is alignment with the shared current
section.

## Countermodel matrix

| # | Insufficiency isolated | Constructive theorem |
| ---: | --- | --- |
| 1 | Nontrivial causal order with no centers | `causal_order_without_observer_centers` |
| 2 | Centers/stages with no records | `centers_and_stages_without_records` |
| 3 | Record-grounded mnemonic node without represented succession | `mnemonic_representation_without_represented_succession` |
| 4 | Represented succession without any lawful total reference frame | `represented_succession_without_self_location` |
| 5 | Canonical current anchor without R1 | `self_location_without_r1` |
| 6 | R0 without R1 | `r0_without_r1`, `exists_r0_not_r1` |
| 7 | R1 without a coherent prospective witness | `r1_without_self_reference_transport`, `exists_r1_not_r2` |
| 8 | Continuation without section preservation | `continuation_without_self_reference_preservation` |
| 9 | Current/projected anchors with no possible lawful action | `current_and_projected_anchors_without_any_lawful_action` |
| 10 | Lawful preserving succession without forecast grounding | `lawful_succession_without_forecast_grounding` |
| 11 | Forecast grounding without the required transport | `forecast_grounding_without_self_reference_transport` |
| 12 | Preserving transport with inaccurate role atlas | `self_reference_transport_with_inaccurate_role_encoding` |
| 13 | Locally correct endpoint shape without identity coherence | `transport_shaped_pair_without_identity_coherence` |
| 14 | Valid mnemonic record grounding without R2 | `mnemonic_record_grounding_without_prospective_de_se` |
| 15 | R2 without record tokens | `r2_without_record_tokens`, `exists_r2_without_records` |
| 16 | R2 without phase-three uptake | `r2_without_functional_uptake` |

`FunctionalUptakePlaceholder := False` is local to the hostile fixture and
serves only as a boundary marker.  No R3 architecture, prediction, judgment,
action, behavior, or functional-use semantics is introduced.

## Provenance decision

Phase two uses Option B.  `traceValid` remains outside R1 and R2.  The old
rhetorically inflated R2 invariance result was removed.  Its replacement,
`trace_validity_definitional_nondependence_for_r1`, is explicitly classified
as a definitional nondependence receipt for R1 only.  It is not counted as a
substantive representational theorem.

This smaller choice keeps records distinct from forecasts and preserves the
constructive R2-without-records boundary.

## Full-signature isomorphism and transport

`FullSignatureIso` transports the original seven sorts—events, observers,
centers, stages, record tokens, forecast tokens, and representation nodes—
plus the new reference-coordinate sort.  It preserves/reflection-connects:

- causal order, ownership, event anchoring;
- stage anchoring and `stageAt`;
- all record fields and `traceValid`;
- all forecast fields;
- node stage, perspective, target, encoded role, and mode;
- `repBefore`, both grounding relations, and continuation candidates;
- `referenceNode`, `currentReference`, and `carry`.

There is deliberately no isomorphism field asserting current-reference
preservation or R2.  Those are recovered from operation preservation.

Constructive biconditionals cover:

- `external_role_shift_transport`;
- `internal_role_encoding_transport`;
- `preserves_current_reference_transport`;
- `coherent_prospective_witness_transport`;
- `coherent_transport_characterization_transport`;
- `prospective_de_se_encoding_transport`.

The inverse witness proof explicitly pulls nodes and forecasts back with the
provided inverse functions and proves endpoint equality by injectivity.  No
choice or quotient is used.

## Axiom, constructivity, and dependency audit

`StaticRole.Campaign.Qualification` runs `#print axioms` for 48 named
theorems spanning the core laws, characterization, every required transport,
all hostile conditions, central same-reduct results, R0/R1/R2 existence
theorems, accuracy, and the demoted provenance receipt.  Every result prints:

```text
does not depend on any axioms
```

| Theorem class | Axiom use |
| --- | --- |
| R0/R1 accuracy and transport | none |
| Reference round-trip, injectivity, composition, reverse | none |
| R2 characterization and remoding invariance | none |
| Eight-sort forward/inverse witness transport | none |
| Ten hostile phase-two separations | none |
| Same-reduct R2 and rich-witness disagreement | none |
| Existence and provenance boundary theorems | none |

There is no `sorry`, `admit`, custom axiom, `Classical`,
`Classical.choice`, quotient, `native_decide`, unsafe declaration, or
partial declaration in `StaticRole`.  There are no Mathlib imports or Lake
package dependencies.  All finite proofs use pattern matching and
constructive elimination.

The structural search also confirms no meta-time, time-indexed model family,
moving selector, global present/now predicate, physical `next`, temporal
logic, category theory, probability, geometry, quantum, thermodynamic, or
phenomenal primitive.

## Verification record

```text
lake build StaticRole
Build completed successfully (23 jobs).

lake build CalculiStable CalculiScratch CalculiAll Calculi
Build completed successfully (269 jobs).

python3 scripts/formalization_audit.py check --skip-external --skip-footprints
FORMALIZATION AUDIT: PASS (19 checks)

git diff --check
[no output; exit 0]
```

The default-target build replays pre-existing governed modules whose printed
axioms are outside this isolated campaign; it completed successfully and no
such module was modified.

## Line-count summary

Physical lines, including comments and blanks:

| Class | Files included | Lines |
| --- | --- | ---: |
| Signature/core | core, information, basic representation, role encoding, succession, expansion | 311 |
| Coherence/transport | self-reference, repaired R2, isomorphism, transport | 1,178 |
| Countermodels | all four finite countermodel modules | 1,243 |
| Theorems | `ExpansionIndependence.lean` | 152 |
| Qualification infrastructure | aggregate root and axiom-audit leaf | 67 |
| Qualification document | this file | 425 |

## Fast-falsification assessment

The repair exceeds phase-one definitional bookkeeping in four specific ways:

1. The primitive `isSelf` predicate is gone.  R2 is invariant under arbitrary
   replacement of `mode`.
2. A carry assignment must satisfy unconditional identity and all-center
   composition, hence round trip and injectivity, and must realize
   continuation through `repBefore`.
3. The critical negative expansion is not made negative by removing nodes,
   forecasts, grounding, continuation, R1, or a transport action.  It uses a
   second globally lawful action over the same literal lower signature.
4. The characterization recovers the decisive reference equality from
   node-level endpoint coherence using injectivity; it is not `Iff.rfl`.

The result is still bounded and representation-relative.  The
`currentReference` section is model structure, and this package does not
claim that every such section is semantically adequate.  The theorem shows
that once a typed frame and its laws are fixed, prospective de se encoding is
a genuine coherence/alignment obligation rather than a free truth-valued
label.  It does not establish a general theory of self-reference or functional
uptake.

The phase-two stop conditions therefore do not fire, and the disposition is:

```text
READY-FOR-OPERATOR-RATIFICATION
```

## Scope statement

> This package formalizes external center-relative temporal roles, internal cross-center role encoding, and prospective de se encoding. It does not formalize temporal passage, phenomenal experience, consciousness, or personal identity.
