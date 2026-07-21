# GT-C03 Public Admission Qualification — Dependency Inventory

**Date:** 2026-07-20

**Campaign:** `GT-C03 Public Admission Qualification`

**Authority:** human rendering of the machine-readable dependency manifest

**Machine manifest:** `GT-C03-DEPENDENCY-INVENTORY.json`
**Machine-manifest SHA-256:** `da65866451a7f065018c701ea078d7b8724b5bf3933f793655ce9a932ff16276`

The JSON manifest is authoritative for path, mode, blob, SHA-256, ownership,
surface-role, and root-effect facts. This record presents the bounded admission
result without copying the full public repository inventory.

## Public base and candidate leaf

```text
public base commit  876ebf953bfa16c135138d9a736c050421ccb7e9
public base tree    00a5eed4ad4657fef9e8918c0662e9f50e89defa

serialization parent  e8954236a3a42c0ad9ed8f40cfc72d80524b0615
parent tree           576ffc003706891918d447a36e97fc0535d1b188

target module       LeanProofs.GovernedTransportEvidence.Instances.SpineProjection
target path         LeanProofs/GovernedTransportEvidence/Instances/SpineProjection.lean
declaration ns      LeanProofs.GovernedTransport.Instances.SpineProjection
target blob         d84c215d9d45334f40c9888336c33e375ce694b0
target SHA-256      03615e67a159cba0b5495b536723c83899dcad98b6271c0b7675e32f0f3f62a0
```

The two commits between the frozen public scientific envelope and the
serialization parent are documentation-only. They change no Lean source, GT
metadata, Lake target, custody registry, or stable-surface registry. Their
documents remain inherited and are not part of the C03 candidate delta.

The leaf has exactly three direct imports:

```text
LeanProofs.Admissibility.Calculus.Instances.Weathering.Spine
LeanProofs.GovernedTransport.Positive
LeanProofs.GovernedTransport.CoverageRepair
```

## Exact transitive dependency closure

The closure below excludes the C03 leaf itself and contains exactly 12 existing
public stable modules.

| Module | Git blob |
| --- | --- |
| `LeanProofs.Admissibility.Calculus.Core` | `961f4d2a1ea7c5d9236338dedf42ded6481d1c3e` |
| `LeanProofs.Admissibility.Calculus.Instances.Weathering` | `4d26acc98ca3879e7c01e13abe3ef2a902caf1a4` |
| `LeanProofs.Admissibility.Calculus.Instances.Weathering.Native` | `b7a356dd6690c6c59ce180eafa46ab030b4816b7` |
| `LeanProofs.Admissibility.Calculus.Instances.Weathering.Obstructions` | `d91638f116908896cfd875874beede5bb4142bf1` |
| `LeanProofs.Admissibility.Calculus.Instances.Weathering.Spine` | `11edea79fdb9f44d6a974113447c6f38bbf92152` |
| `LeanProofs.Admissibility.Calculus.Spine` | `c2c9208fcd1ce41c32329d4ba5074b924e13a0cc` |
| `LeanProofs.Admissibility.PathVerdict.Core` | `2ea8ac303376a772e6182bb62452db0ccbc191f2` |
| `LeanProofs.GovernedTransport.Composition` | `ab9011a1f676c7e7d0bcdd8d80e3e831de8ed288` |
| `LeanProofs.GovernedTransport.Core` | `275580b4fc8a5c5a7b667d80bb7f6c65efe0fe2c` |
| `LeanProofs.GovernedTransport.Coverage` | `73562656320e1d8d534872aab1df0cd4de1d4762` |
| `LeanProofs.GovernedTransport.CoverageRepair` | `e8e656d67829c55802f1edaef224ca55727c0d26` |
| `LeanProofs.GovernedTransport.Positive` | `0743f6e2129a7fcb1733a7a23bc7527fad03856b` |

Every closure member is classified `STABLE-SURFACE`. The machine audit records:

```text
hostile fixture dependency          false
private campaign dependency         false
skunkworks namespace dependency     false
temporary infrastructure dependency false
Mathlib dependency                  false
forbidden dependency count          0
```

## Source import sanitation

The frozen source leaf remains:

```text
path  formalization/Calculi/Scratch/GovernedTransport/Instances/SpineProjection.lean
blob  37bea51190157023c521d8e8f71912f1485cf9e8
```

Its four source imports were treated as follows:

| Source import | Disposition |
| --- | --- |
| `Calculi.Scratch.CrossCalculus.WeatheringSpine` | mapped to its exact admitted public endpoint |
| `Calculi.Scratch.CrossCalculus.LosslessEncodingCollapse` | unused adverse evidence; deliberately absent from the target closure |
| `Calculi.Scratch.GovernedTransport.Positive` | mapped to the exact admitted public GT leaf |
| `Calculi.Scratch.GovernedTransport.CoverageRepair` | mapped to the exact admitted public GT leaf |

Removing the unused hostile import did not remove a declaration or elaboration
dependency: the compiled source/target declaration manifest remains total,
injective, and exact for all 82 declarations.

## K05 and K18

K05 remains separately pinned source adverse evidence:

```text
path    formalization/Calculi/Scratch/CrossCalculus/LosslessEncodingCollapse.lean
blob    b448b82cd248ecedb926bd95938ccf958044ac92
SHA-256 386cbf96af650620e983619f1a179ad8a6d6bb1bf6d36fc519b22b786f86ab9a
```

It is not claimed as a public executable hostile module and is not in the C03
target import closure. Its exact non-collapse side remains visible through the
already-public controls:

```text
Admissibility.Calculus.LosslessEncoding.encodePacket_injective
Admissibility.Calculus.LosslessEncoding.distinct_refusals_encode_distinct
Admissibility.Calculus.LosslessEncoding.no_subsingleton_domain_of_distinct_refusals
Admissibility.Calculus.Instances.Weathering.weather_funnel_distinguishes_stale_and_retired
```

K18 is carried by the admitted C03 leaf itself through:

```text
missingWitness_exhibited_gap
weatherBridge_not_target_covered
missingWitness_has_no_imported_positive
missingWitness_has_no_imported_negative
missingWitness_target_local_is_not_transported
```

Thus neither knife is laundered into the stable generic root: K05 remains a
separately bound adverse witness and K18 remains exact instance evidence.

## Public-root effect

The stable `LeanProofs.GovernedTransport` root is byte-exact and retains its ten
stable leaves. The repository root, `lakefile.toml`, stable-surface registry,
and public-target registry are unchanged.

The public-evidence aggregate changes by exactly one direct import of the C03
evidence leaf:

```text
base aggregate blob       bbb92b0c82d100a1dd0baac662aba36730c059c0
candidate aggregate blob  b455ee8d66498b1126a599932406fe96fa7d2420
aggregate + closure       21 modules
```

This is evidence-surface admission, not stable-surface expansion. It neither
changes the GT core contract nor makes C03 transitively reachable from the
stable GT root.

The public-custody registry receives exactly one `PUBLIC-EVIDENCE` row for the
C03 leaf (`acc0cd8a0663b20d2eb16683b665183e818eb64b` →
`2197691fab61613c82d2a2e5bba22d2dabad4406`). This records the candidate leaf;
it does not change the stable-surface or public-target registries.

## Dependency conclusion

C03 depends only on already-public GT and admissibility infrastructure after
the exact declared import sanitation. It introduces no hidden private,
campaign, hostile, scratch, temporary, or namespace-laundered dependency. Its
admission changes no existing disposition: C03 remains boundedly
`SECONDARY-QUALIFIED`; C01 and C02 are not transferred; C04 remains unresolved;
and no generic extension, global coverage, composition, repair, target custody,
spend, obligation, origin, or history law is added.
