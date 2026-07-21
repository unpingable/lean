# GT-C03 Target Custody Record

**Date:** 2026-07-20

**Candidate verdict:** `C03-PUBLIC-ADMISSION-RATIFIED`

**Custody state:** `ACTIVE`

The exact candidate target envelope is active under the operator decision
`RATIFY-C03-PUBLIC-ADMISSION`. This activation does not alter scientific
ownership or modify the stable public GT contract.

## Revision chain

```text
public base commit       876ebf953bfa16c135138d9a736c050421ccb7e9
public base tree         00a5eed4ad4657fef9e8918c0662e9f50e89defa

candidate commit         769cba86a12cf6788b88916d140acc4e9fd78af7
candidate tree           42ee31f7b513400c5fb9c51440be4e205a651a24
candidate parent         e8954236a3a42c0ad9ed8f40cfc72d80524b0615
parent tree              576ffc003706891918d447a36e97fc0535d1b188

custody activation       ACTIVE — containing commit
activation parent        4f8fa3ca5d9902869c6aa5de091af75bfb1a823f
operator record          docs/GT-C03-OPERATOR-RATIFICATION_2026-07-20.md
```

The activation revision is the commit containing this record; this avoids a
self-referential commit identifier. Its exact commit, tree, and parent are
reported by Git after serialization. The operator record binds the immutable
candidate and manifest identities.

The serialization parent is a documentation-only descendant of the frozen
public scientific envelope. The intervening commits `51b9e3a...` and
`e895423...` change no Lean source, GT custody metadata, Lake target, or public
surface registry; their documentation remains inherited and outside this
candidate's thirteen-path delta.

## Frozen scientific source

```text
source scientific commit c46d1d925b736ab753524ac2c90504fcc7dcf1ae
source scientific tree   2d500f5a8ba8e02cb532bfcb130beb00a99da5bc
source leaf blob          37bea51190157023c521d8e8f71912f1485cf9e8
source leaf path          formalization/Calculi/Scratch/GovernedTransport/Instances/SpineProjection.lean
private disposition       SECONDARY-QUALIFIED
```

The GT-4A source and public crossing remain closed. This candidate neither
regenerates their packet nor makes itself a retroactive condition of their
validity.

## Exact target object

```text
target leaf path          LeanProofs/GovernedTransportEvidence/Instances/SpineProjection.lean
target module             LeanProofs.GovernedTransportEvidence.Instances.SpineProjection
declaration namespace     LeanProofs.GovernedTransport.Instances.SpineProjection
target leaf blob          d84c215d9d45334f40c9888336c33e375ce694b0
target leaf SHA-256       03615e67a159cba0b5495b536723c83899dcad98b6271c0b7675e32f0f3f62a0
surface role              PUBLIC-EVIDENCE
```

The candidate changes the declaration-free evidence aggregate by one import
of this leaf. It does not change the stable root, repository root, Lake target
set, target registry, or stable-surface registry.

## Candidate path surface

The serialized candidate is expected to contain exactly these thirteen paths:

```text
LeanProofs/GovernedTransportEvidence.lean
LeanProofs/GovernedTransportEvidence/Instances/SpineProjection.lean
docs/GT-C03-ADMISSION-RATIONALE_2026-07-20.md
docs/GT-C03-DECLARATION-INVENTORY.json
docs/GT-C03-DECLARATION-INVENTORY_2026-07-20.md
docs/GT-C03-DEPENDENCY-INVENTORY.json
docs/GT-C03-DEPENDENCY-INVENTORY_2026-07-20.md
docs/GT-C03-HOSTILE-REVIEW_2026-07-20.md
docs/GT-C03-PUBLIC-COMPATIBILITY-RECEIPT_2026-07-20.md
docs/GT-C03-TARGET-CUSTODY-CANDIDATE_2026-07-20.md
scripts/check-gt-c03-admission.py
scripts/gt-c03-declaration-dump.lean.in
scripts/public-custody.tsv
```

Any extra or missing path blocks ratification unless the operator explicitly
authorizes a corrected candidate surface.

## Bound inventories

```text
declaration inventory SHA-256
3ef48396531a560cf31b28ecbf08bdf725de0b06a835629a980467b5cd41f700

dependency inventory SHA-256
da65866451a7f065018c701ea078d7b8724b5bf3933f793655ce9a932ff16276
```

The declaration inventory binds 82 compiled declarations: 72 axiom-free and
ten exactly `[propext]`, with zero other axiom sets and zero
`Classical.choice`. It also binds the historical 17-receipt footprint: eleven
axiom-free and six exactly `[propext]`, and the nine registered theorem
commands.

The dependency inventory binds the exact 12-module already-public stable
dependency closure, zero prohibited dependencies, protected-root identities,
K05's separate posture, and the K18 receipts carried by the leaf.

## Verification bound to the candidate bytes

```text
direct C03 target build                         PASS — 14 jobs
GovernedTransportEvidence aggregate build      PASS — 23 jobs
exact source/target checker                     PASS — 82/82
hostile checker self-test                       PASS — 8/8
public custody audit                            PASS — 217/115/101/1
registered target audit                         PASS — 26 targets
stable GT root                                  BYTE-EXACT
existing GT-4A 704 declaration-bearing leaves  BYTE-EXACT
```

The frozen source hostile K05 remains private and separately identified. The
public repaired non-collapse controls remain exact. K18 is present in the
target C03 leaf. Neither knife is laundered into a stronger disposition.

## Custody-role split

Under the operator ratification of this exact candidate:

- the public repository may hold target custody for the exact C03 evidence
  leaf and expose it through the public evidence aggregate;
- Skunkworks remains canonical scientific development owner of the source
  theory and historical hostile laboratory;
- the stable public GT core remains under its existing compatibility custody;
- no general scientific ownership transfer occurs; and
- internal qualification plus public availability still do not constitute
  external validation or endorsement.

The current states are:

```text
C03 public admission                 RATIFIED
C03 target custody                   ACTIVE
C03 public compatibility             ACTIVE
stable public GT surface             UNCHANGED
GT-4A source/public custody           CLOSED; NOT REOPENED
canonical scientific ownership       SKUNKWORKS
runtime correspondence               INACTIVE
external validation                  NOT CLAIMED
release/tag/DOI                       NOT CREATED BY THIS CAMPAIGN
```

## Nonclaims retained

This candidate does not establish target-global coverage, governed
composition, associativity, exact repair, target custody transport, spend or
obligation transport, origin/history preservation, a generic extension,
standalone coverage-debt algebra, C01/C02 admission, C04 resolution, runtime
conformance, empirical validation, public endorsement, or general ownership
transfer.

## Operator gate

The exact serialized candidate passed independent operator review and was
ratified by `RATIFY-C03-PUBLIC-ADMISSION`. Any later change to its path
surface, leaf blob, manifests, declaration correspondence, axiom footprint,
dependency closure, K05/K18 posture, stable-root identity, or bounded
disposition is a new object and is not covered by this activation.
