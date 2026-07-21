# GT-C03 Public Compatibility Receipt

**Date:** 2026-07-20

**Campaign:** `GT-C03 Public Admission Qualification`

**Candidate verdict:** `C03-PUBLIC-ADMISSION-CANDIDATE`

**Receipt posture:** target-candidate compatibility established; operator
ratification and target custody activation remain pending.

## Governed objects

The public candidate is based on the already-ratified GT-4A target envelope:

```text
public base commit  876ebf953bfa16c135138d9a736c050421ccb7e9
public base tree    00a5eed4ad4657fef9e8918c0662e9f50e89defa

serialization parent  e8954236a3a42c0ad9ed8f40cfc72d80524b0615
parent tree           576ffc003706891918d447a36e97fc0535d1b188
```

The serialization parent is a documentation-only descendant of the public
scientific envelope. Its two intervening commits change zero Lean paths and
zero GT metadata, Lake-target, or public-surface registry paths. Those
unrelated documents are inherited, not part of this campaign's delta.

The unchanged C03 scientific source is the Stage-3 object:

```text
source commit       c46d1d925b736ab753524ac2c90504fcc7dcf1ae
source tree         2d500f5a8ba8e02cb532bfcb130beb00a99da5bc
source path         formalization/Calculi/Scratch/GovernedTransport/Instances/SpineProjection.lean
source blob         37bea51190157023c521d8e8f71912f1485cf9e8
```

The exact candidate leaf is:

```text
target path         LeanProofs/GovernedTransportEvidence/Instances/SpineProjection.lean
target module       LeanProofs.GovernedTransportEvidence.Instances.SpineProjection
target namespace    LeanProofs.GovernedTransport.Instances.SpineProjection
target blob         d84c215d9d45334f40c9888336c33e375ce694b0
target SHA-256      03615e67a159cba0b5495b536723c83899dcad98b6271c0b7675e32f0f3f62a0
```

No candidate commit or tree is recorded yet. The work remains an inactive
custody candidate until an operator ratifies exact serialized revisions.

## Exact declaration correspondence

The machine-readable declaration inventory is
`docs/GT-C03-DECLARATION-INVENTORY.json`, with SHA-256:

```text
3ef48396531a560cf31b28ecbf08bdf725de0b06a835629a980467b5cd41f700
```

It establishes an injective source-to-target correspondence for all 82
compiled declarations owned by the C03 leaf, including declarations generated
by Lean for its three structures. The source and target agree on declaration
kind, canonical universe parameters, normalized type, normalized body or
value, declaration-content digest, and axiom set under the recorded namespace
and public-endpoint mappings.

The exact target footprint is:

```text
compiled declarations             82
command-level declarations         25
registered theorem commands         9
printed receipts                   17

axiom-free compiled declarations   72
exactly [propext]                   10
other or mixed axiom sets            0
Classical.choice                     0

printed receipts axiom-free         11
printed receipts [propext]           6
```

No declaration drift or axiom drift was found. A smaller axiom footprint
would also have been treated as drift rather than as an automatic
improvement.

## Dependency result

The machine-readable dependency inventory is
`docs/GT-C03-DEPENDENCY-INVENTORY.json`, with SHA-256:

```text
da65866451a7f065018c701ea078d7b8724b5bf3933f793655ce9a932ff16276
```

The target leaf has exactly three direct imports:

```text
LeanProofs.Admissibility.Calculus.Instances.Weathering.Spine
LeanProofs.GovernedTransport.Positive
LeanProofs.GovernedTransport.CoverageRepair
```

Its complete transitive dependency closure, excluding the leaf itself, is 12
already-public `STABLE-SURFACE` modules. The closure contains no hostile
fixture, private campaign module, skunkworks namespace, temporary proving
module, or Mathlib dependency.

The private source import
`Calculi.Scratch.CrossCalculus.LosslessEncodingCollapse` contributes no
referenced declaration, instance, attribute, or exported environment effect.
It is deliberately absent from the target closure. Removing that unused
adverse-evidence import does not remove K05; K05 remains separately bound as
described below.

## Public surface effect

The public stable root `LeanProofs.GovernedTransport`, its ten stable leaves,
the repository root `LeanProofs`, `lakefile.toml`, the target registry, and the
stable-surface registry remain byte-exact.

The 704 declaration-bearing GT-4A leaves remain byte-exact: 460 stable and 244
existing evidence declarations are neither rewritten nor requalified. The
only aggregate change is one import added to the declaration-free
`LeanProofs.GovernedTransportEvidence` aggregate for the exact C03 evidence
leaf. C03 contributes 82 separately inventoried public-evidence declarations;
it does not become part of the stable public GT surface.

The custody registry adds exactly one `PUBLIC-EVIDENCE` leaf. Candidate audit
accounting is:

```text
public sources          217
stable                  115
public evidence         101
aggregates                1
registered targets       26
```

No import is added to the stable or repository root. The single evidence-root
import described above is the complete root effect. No Lake target,
stable-surface registration, or constitutional-core declaration is
introduced.

## K05 and K18

K05 remains exact but separate. Its frozen source adverse specimen is:

```text
path  formalization/Calculi/Scratch/CrossCalculus/LosslessEncodingCollapse.lean
blob  b448b82cd248ecedb926bd95938ccf958044ac92
```

The public target already carries the repaired non-collapse controls:

- `LosslessEncoding.encodePacket_injective`;
- `LosslessEncoding.distinct_refusals_encode_distinct`;
- `LosslessEncoding.no_subsingleton_domain_of_distinct_refusals`; and
- `weather_funnel_distinguishes_stale_and_retired`.

C03 consumes the exact `LosslessEncoding` endpoint. It does not import the
private hostile specimen and does not claim that K05 is a newly admitted
public executable module.

K18 is carried by the target leaf itself through the exact
`missingWitness` gap, local-refusal, no-imported-positive,
no-imported-negative, and combined non-transport theorems. The target-local
verdict is not reclassified as transported evidence.

## Executed verification

The candidate checks reported:

```text
direct C03 target build                         PASS (14 jobs)
GovernedTransportEvidence aggregate build      PASS (23 jobs)
exact correspondence checker                   PASS (82/82)
checker hostile self-test                      PASS (8/8)
public custody audit                           PASS (217/115/101/1)
registered-target audit                        PASS (26 targets)
```

The hostile self-test fails closed for a missing declaration, an extra
declaration, kind drift, type drift, body drift, axiom drift, a target-name
collision, and dependency-closure drift. The separate hostile review audits
the bounded disposition, K05/K18 posture, and protected-root identities.

Historical GT campaigns and the GT-4A packet were not regenerated or
requalified. Their frozen facts are reused by exact revision, tree, blob, and
inventory identities.

## Compatibility boundary

This receipt establishes candidate compatibility only. It does not establish:

- operator ratification or active C03 custody;
- a change to the stable public Governed Transport contract;
- target-global coverage;
- governed composition or associativity for C03;
- exact coverage repair;
- target custody, spend, obligation, origin, or history transport;
- C01 or C02 public admission;
- C04 resolution;
- a generic extension or coverage-debt object;
- runtime correspondence, empirical validation, or external endorsement; or
- release, tag, DOI, publication, or general ownership transfer.
