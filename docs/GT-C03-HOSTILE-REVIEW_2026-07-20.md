# GT-C03 Public Admission Qualification — Hostile Review

**Date:** 2026-07-20

**Campaign:** `GT-C03 Public Admission Qualification`

**Review result:** None of H01 through H16 established a refusal witness.

This is a bounded review of the exact C03 public-evidence candidate. It does
not reopen GT-4A, redesign the Governed Transport core, enlarge the stable
surface, activate target custody, or authorize a later campaign.

## Exact reviewed object

The source object remains:

```text
path  formalization/Calculi/Scratch/GovernedTransport/Instances/SpineProjection.lean
blob  37bea51190157023c521d8e8f71912f1485cf9e8
```

The proposed target object is:

```text
path       LeanProofs/GovernedTransportEvidence/Instances/SpineProjection.lean
module     LeanProofs.GovernedTransportEvidence.Instances.SpineProjection
namespace  LeanProofs.GovernedTransport.Instances.SpineProjection
role       PUBLIC-EVIDENCE
```

It imports exactly:

```text
LeanProofs.Admissibility.Calculus.Instances.Weathering.Spine
LeanProofs.GovernedTransport.Positive
LeanProofs.GovernedTransport.CoverageRepair
```

The target leaf has exactly twelve transitive public dependencies, all
already-public stable modules, and zero forbidden dependencies. The private
`LosslessEncodingCollapse` import is absent.

## Positive baseline

The source-derived declaration inventory and freshly compiled target census
agree on all 82 module-owned declarations, including generated declarations:

```text
compiled declarations       82
definitions                 46
theorem-kind constants      27
inductives                    3
constructors                  3
recursors                     3
axiom-free                   72
exactly [propext]            10
other axiom sets              0
Classical.choice              0
```

Names, declaration kinds, canonical universe parameters, normalized types,
normalized bodies or values, and exact axiom sets match 82/82. The
command-level surface remains 25 declarations, including nine theorem
commands. All seventeen printed receipts reproduce: eleven are axiom-free and
six depend exactly on `[propext]`.

The executable checker passed its ordinary gate and rejected all eight
synthetic mutations in `--self-test`: missing declaration, extra declaration,
kind drift, type drift, body drift, axiom drift, namespace collision, and
dependency-closure drift.

The isolated builds also completed:

```text
C03 target leaf       PASS — 14 jobs
public evidence root  PASS — 23 jobs
```

## H01–H16

| Case | Hostile attempt | Detector and observed result |
| --- | --- | --- |
| H01 | Add, remove, rename, or change the kind of a declaration, including a generated declaration. | The complete module-owned roster is exact at 82/82. Synthetic missing, extra, and kind-drift mutations were refused. No declaration drift survived. |
| H02 | Change a declaration type while retaining its expected name. | Canonical normalized type digests match for all 82 declarations. The injected type mutation was refused. |
| H03 | Replace a proof or definition body while retaining its type. | Canonical normalized body/value digests match for every declaration with a value. The same-name body mutation was refused. Definitional or propositional equivalence is not accepted as identity. |
| H04 | Add or remove an axiom while leaving the declaration compilable. | Exact per-declaration set equality gives 72 axiom-free and ten exactly `[propext]`, with no other set. The injected `Classical.choice` mutation was refused. A removed axiom would likewise fail equality. |
| H05 | Reach a hostile fixture, private campaign module, Skunkworks namespace, or temporary proving module through a direct or transitive import. | The leaf has exactly three direct imports and a twelve-module transitive closure. Every node is an already-public stable module; the forbidden count is zero. The dependency-closure mutation was refused. |
| H06 | Hide a private dependency in an elaborated declaration while presenting clean-looking import text. | Exact normalized values and types were derived from the frozen source environment and reproduced in the public environment. All 82 declarations match without a private constant or module in the target closure. No hidden dependency survived. |
| H07 | Make the apparent public rebase depend upon the excluded `LosslessEncodingCollapse` infrastructure. | The target compiles without that import and still reproduces all 82 source-derived declaration types, values, kinds, universes, and axiom sets. The excluded import therefore contributes no required elaboration result. |
| H08 | Launder names through an incomplete, colliding, many-to-one, or alias-producing namespace rewrite. | The declaration map is total and injective. It uses owner-specific endpoint mappings rather than a blanket `CrossCalculus` rewrite. The injected target-name collision was refused, and no alias was introduced. |
| H09 | Drop K05, import its private hostile module publicly, or weaken exact refusal identity into an authority-equivalent bit. | K05 remains pinned separately at source blob `b448b82cd248ecedb926bd95938ccf958044ac92`; it is not a target import and is not described as a public executable hostile module. The already-public exact controls `encodePacket_injective`, `distinct_refusals_encode_distinct`, `no_subsingleton_domain_of_distinct_refusals`, and `weather_funnel_distinguishes_stale_and_retired` remain available. Refusal-identity collapse was not admitted. |
| H10 | Relabel the target-local `.missingWitness` verdict as transported evidence or erase its image gap. | The target carries all five exact K18 results: `missingWitness_exhibited_gap`, `weatherBridge_not_target_covered`, `missingWitness_has_no_imported_positive`, `missingWitness_has_no_imported_negative`, and `missingWitness_target_local_is_not_transported`. Their exact declarations and axiom sets reproduce. |
| H11 | Widen C03 into target-global coverage, composition, associativity, exact repair, target custody, spend, obligation, origin/history transport, or a semantic refusal from decoder `none`. | No candidate declaration states any such result. The exact source declarations and their bounded nonclaims are preserved; `weatherBridge_not_target_covered` and the K18 family actively retain the coverage and provenance boundary. |
| H12 | Smuggle C03 into the stable root or alter stable ownership, Lake targets, or target registration. | The stable aggregate and all ten stable leaves are byte-exact. `lakefile.toml`, `stable-surfaces.tsv`, `public-targets.tsv`, and the repository aggregate are byte-exact. Only the public-evidence aggregate adds the one C03 import. Custody audits close at 217 sources: 115 stable, 101 evidence, and one repository aggregate; twelve stable roots and 26 public targets remain. |
| H13 | Use C03 admission to imply C01 or C02 transfer, C04 resolution, a generic extension, `FEDERATED-OR-NONE`, runtime correspondence, or external validation. | None of those objects or claims appears in the target declaration or dependency surface. C03 remains one bounded instance-level public-evidence object; the inherited dispositions and nonclaims are unchanged. |
| H14 | Establish correspondence against an unpinned, substituted, or redesigned endpoint. | The dependency inventory binds public base commit `876ebf953bfa16c135138d9a736c050421ccb7e9`, tree `00a5eed4ad4657fef9e8918c0662e9f50e89defa`, and every mode, blob, and SHA-256 in the twelve-module closure. The target compiled against those exact endpoints. The serialization parent `e895423...` is separately identified as a documentation-only descendant with zero intervening Lean or GT-metadata changes. |
| H15 | Obtain apparent success by importing a broad aggregate that carries excluded instances or campaign infrastructure. | The target imports the exact Weathering spine leaf and two exact GT leaves, not an Admissibility, repository, Stage, or campaign aggregate. Its complete closure contains no BreakGlass, C01, C02, C04, private adapter, hostile fixture, or temporary helper. |
| H16 | Alter a public root or aggregate beyond the exact admitted evidence object. | The stable root is unchanged at ten leaves, eleven modules including its aggregate. The evidence root changes by exactly one direct import and closes at twenty dependencies, twenty-one modules including its aggregate. The repository aggregate's direct imports remain unchanged. No second root or registry edge was added. |

## K05 and K18 boundary

K05 and K18 have different custody roles and are not conflated by admission:

- K05 remains frozen Skunkworks adverse evidence plus already-public exact
  non-collapse controls. It is scientific review evidence, not a target
  dependency and not newly claimed as public executable hostile code.
- K18 is part of the exact C03 object. Its target-local refusal, exhibited
  image gap, noncoverage, and absence of imported positive and negative
  evidence remain compiled public evidence.

This separation defeats both hostile directions: importing excluded private
machinery merely to make C03 compile, and presenting C03 publicly after
discarding its load-bearing loss and provenance knives.

## Constitutional and custody result

C03 instantiates existing public `Span`, `CandidateLift`, `TranslateAlong`,
`RelyLocally`, coverage, gap, `GovernedFamily`, `LosslessEncoding`, and
`PathVerdict` infrastructure. It adds no generic definition or law and changes
no compatibility-bearing root. Its one evidence-aggregate import is
distribution contact for a `PUBLIC-EVIDENCE` leaf, not stable-surface
membership.

No hostile attempt established declaration drift, axiom drift, hidden private
dependency, namespace laundering, disposition widening, or dependence upon
excluded infrastructure. This review supplies no custody activation, public
ratification, ownership transfer, runtime correspondence, external
validation, release, tag, DOI, push, or subsequent-campaign authority.
