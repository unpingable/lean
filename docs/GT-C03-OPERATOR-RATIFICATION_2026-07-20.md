# GT-C03 Operator Ratification

**Date:** 2026-07-20

**Operator decision:** `RATIFY-C03-PUBLIC-ADMISSION`

**Disposition:** `RATIFIED`

This record accepts only the exact serialized C03 public-admission candidate
below. The Git commit containing this record is the public-custody activation
revision; its parent is recorded below so the activation remains on the exact
candidate's direct linear ancestry.

## Exact candidate identity

```text
candidate commit  769cba86a12cf6788b88916d140acc4e9fd78af7
candidate tree    42ee31f7b513400c5fb9c51440be4e205a651a24
candidate parent  e8954236a3a42c0ad9ed8f40cfc72d80524b0615

activation parent 4f8fa3ca5d9902869c6aa5de091af75bfb1a823f
```

The activation parent differs from the candidate only by the two inherited
documentation paths under `docs/calculus/` introduced by the operator's
`doc updates` commit. It changes no governed Lean source, import, proof,
declaration or dependency manifest, custody registry, target registry, stable
surface, or C03 qualification receipt.

## Bound manifest identities

```text
declaration manifest SHA-256
3ef48396531a560cf31b28ecbf08bdf725de0b06a835629a980467b5cd41f700

dependency manifest SHA-256
da65866451a7f065018c701ea078d7b8724b5bf3933f793655ce9a932ff16276
```

The operator ratification reuses the candidate's frozen `82/82` declaration
correspondence, compiled and printed axiom footprints, three direct imports,
12-module public-only dependency closure, K05/K18 dispositions, protected-root
and 704-declaration byte identities, one-import evidence aggregation, hostile
`8/8` result, custody accounting `217/115/101/1`, and public-target result
`26/26`. None of those scientific qualification checks is rerun by this
activation.

## Activated state

```text
C03 public admission                 RATIFIED
C03 public custody                   ACTIVE
C03 public compatibility             ACTIVE
stable public GT core                UNCHANGED
existing GT-4A 704 declarations      BYTE-EXACT
C03 evidence aggregation             ACTIVE AS QUALIFIED
K05                                  SEPARATELY PINNED
K18                                  FULLY CARRIED BY C03
```

## Boundaries retained

```text
C01 public admission                 INACTIVE
C02 public admission                 INACTIVE
C04 public admission                 INACTIVE
general ownership transfer           INACTIVE
runtime correspondence               INACTIVE
external validation                  NOT CLAIMED
release/tag/DOI                       UNCHANGED
```

This act neither widens the stable GT root nor ratifies any other candidate.
It creates no release, publication, DOI, runtime-conformance claim, or general
scientific ownership transfer.
