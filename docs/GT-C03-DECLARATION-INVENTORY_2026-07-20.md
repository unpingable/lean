# GT-C03 Public Admission Qualification — Declaration Inventory

**Date:** 2026-07-20

**Campaign:** `GT-C03 Public Admission Qualification`

**Authority:** human rendering of the machine-readable declaration manifest

**Machine manifest:** `GT-C03-DECLARATION-INVENTORY.json`
**Machine-manifest SHA-256:** `3ef48396531a560cf31b28ecbf08bdf725de0b06a835629a980467b5cd41f700`

The JSON manifest is authoritative for the complete declaration-by-declaration
mapping, normalized type and value digests, kinds, level parameters, and axiom
sets. This record summarizes that exact object; it does not create a second
hand-maintained declaration inventory.

## Bound source and target

```text
source path       formalization/Calculi/Scratch/GovernedTransport/Instances/SpineProjection.lean
source blob       37bea51190157023c521d8e8f71912f1485cf9e8
source namespace  Calculi.Scratch.GovernedTransport.Instances.SpineProjection

target path       LeanProofs/GovernedTransportEvidence/Instances/SpineProjection.lean
target blob       d84c215d9d45334f40c9888336c33e375ce694b0
target SHA-256    03615e67a159cba0b5495b536723c83899dcad98b6271c0b7675e32f0f3f62a0
target namespace  LeanProofs.GovernedTransport.Instances.SpineProjection
```

The physical target module is deliberately packaged under the public-evidence
tree. Its declarations retain the governed-transport instance namespace. This
does not add the instance to the stable `LeanProofs.GovernedTransport` root.

## Exact compiled footprint

```text
compiled declarations       82
  definitions               46
  theorems                   27
  inductives                  3
  constructors                3
  recursors                   3

axiom-free                   72
exactly [propext]            10
other axiom sets              0
Classical.choice              0

command-level declarations   25
printed receipts             17
  axiom-free                 11
  exactly [propext]           6
registered theorem commands   9
```

The difference between 25 source commands and 82 compiled declarations is
expected: the three source structures generate constructors, recursors,
projections, size functions, and associated theorem declarations. All of those
generated declarations are included in the 82-row machine manifest. The
17-receipt footprint is the frozen scientific receipt surface; it is not used
as a substitute for compiled-declaration preservation.

## Preservation result

For all 82 declarations, the machine comparison records:

```text
source count equals target count        true
name map total and injective             true
declaration kind equal                   true
normalized type equal                    true
normalized value/body equal              true
axiom set equal                          true
preservation class                       ALPHA-RENAMED-NAMESPACE-ONLY
```

No source declaration is omitted, duplicated, or mapped ambiguously. No target
declaration acquires a different kind, normalized type, normalized value, or
axiom set.

## Command-level surface

The following table identifies the 25 authored commands. Generated declarations
belong to their originating structures and remain enumerated only in the JSON
manifest.

| Source command | Source kind | Exact axiom set |
| --- | --- | --- |
| `bridge` | definition | none |
| `sourceCandidateLift` | definition; printed receipt | none |
| `coveredFunnelTarget` | definition; printed receipt | none |
| `ImportedPositive` | structure | none |
| `translatePositive` | definition; printed receipt | none |
| `TargetAuthority` | abbreviation | none |
| `relyPositive` | definition; printed receipt | none |
| `transportPositive` | definition; printed receipt | none |
| `DecidedRefusal` | structure | none |
| `ImportedNegative` | structure | none |
| `translateNegative` | definition; printed receipt | none |
| `TargetRefusal` | abbreviation | none |
| `relyNegative` | definition; printed receipt | none |
| `importedNegative_exact_refusal_recovery` | theorem; printed receipt | `[propext]` |
| `authority_nonamplification` | theorem; printed receipt | none |
| `target_authority_retains_source_authority_and_custody` | theorem; printed receipt | none |
| `importedPositive_retains_source_custody` | theorem; printed receipt | none |
| `weatherBridge` | definition | none |
| `missingWitnessVerdict` | definition | none |
| `missingWitness_target_local_refusal` | theorem; printed receipt | none |
| `missingWitness_exhibited_gap` | definition; printed receipt | `[propext]` |
| `weatherBridge_not_target_covered` | theorem; printed receipt | `[propext]` |
| `missingWitness_has_no_imported_positive` | theorem; printed receipt | `[propext]` |
| `missingWitness_has_no_imported_negative` | theorem; printed receipt | `[propext]` |
| `missingWitness_target_local_is_not_transported` | theorem; printed receipt | `[propext]` |

The nine commands explicitly authored with `theorem` remain the registered
non-boilerplate theorem footprint. Generated projection and structure theorems
explain why the compiled manifest contains 27 declarations classified by Lean
as theorems; they do not inflate the scientific theorem-command count.

## Scientific boundary preserved

The declaration correspondence preserves C03's bounded facts: exact source
lift, point coverage, positive and negative import, exact refusal recovery,
authority non-amplification, source-custody retention, and the
`missingWitness` target-local/image boundary.

It does not establish target-global coverage, governed composition,
associativity, exact repair, target custody, spend or obligation transport,
origin/history transport, a semantic refusal from decoder `none`, or a generic
extension. The declaration match therefore preserves the existing
`SECONDARY-QUALIFIED` boundary rather than widening it.
