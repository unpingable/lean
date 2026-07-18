# v14 Release Ledger — Governed Admissibility Calculus

**Release status: prepared locally; the annotated tag, GitHub release, and
Zenodo version deposit are pending operator action and are not asserted
here.** Baseline: `v13.0.0`
(`54ffd53fa61d179b8b15f9195e877e1fefcfbd27`, 2026-07-17). Repository
version metadata is `14.0.0` in `lakefile.toml`; `CITATION.cff` carries the
title `Governed Admissibility Calculus`, version `14.0.0`, release date
`2026-07-18`, and concept DOI `10.5281/zenodo.20369489`. The
version-specific DOI is assigned externally when the GitHub release drives
the deposit and is intentionally not guessed here.

## Scope

v14 is the Governed Admissibility Calculus: the seven-rung promotion
campaign that moved the repository's central claim from "several formal
families and their refusal boundaries" to "the indexed compositional
system governing them" — and, as a separate terminal act, ratified the
capital-C name the repository had reserved since v10.

Each rung was a separately hostile-reviewed, operator-ratified,
parity-proven, custody-closed public bundle. Per-rung packets, pins,
fences, and verification receipts live in
[`V14-READINESS-LEDGER.md`](V14-READINESS-LEDGER.md); claim-level entries
are `CLAIM-REGISTER.md` #19–#25.

## Admission history (frozen)

| Rung | Content | Admission commit | Correction consumed |
| ---: | --- | --- | --- |
| 1 | PathVerdict `Domains`/`Located` substrate | `538cf0b2ff2b88087fb6372ec45a6ba611a81db0` | — |
| 2 | `GovernedFamily` signature (`Admissibility.Calculus` established) | `8b93d459683602dfb497686283f082eaa53b9f36` | — |
| 3 | Weathering + BoundedPaidReachability instances | `f0f313107fa318637a4b58b8f014953dd988000c` | — |
| 4 | Exact refusal-packet spine + instance adapters | `6c026d122ce4ac413ff02529243ea0c6581183e6` | `9f24240d92cc…` |
| 5 | Indexed comparison framework (concrete ledger stays evidence) | `dc9c8df51cb785ebbfd130200f195332a14f8be6` | `ba7590af751e…` |
| 6 | Stored-decision crossing + witnessed inhabitant | `41510aa94f50d61f8c807137b17a3b799d7ef66d` | `721c2c8c18e2…` |
| 7 | Origin/history-bound BreakGlass terminal instance | `5a92e17a61cfa65ad7c096c85999801c137cc28d` | `edb5df5…`, `34cc963…` |

**Naming ratification (separate act, 2026-07-18):** rung-7 custody closed
at research-tree commit `62ac346b1fdcbe7e7a66e526595f72ac912ea8df`
(`ADMISSIBILITY_CALCULUS_RUNG7_TRANSFER_RECEIPT_2026-07-18.md`); the
capital-C act is
`ADMISSIBILITY_CALCULUS_CAPITAL_C_RATIFICATION_2026-07-18.md` at
`d5d5f2a9c1c6900e6598d9bea3dc2004d9b113ad`, pinned to that custody base.
The v10 reservation of the word "calculus" is discharged, not repealed.

## Frozen public accounting

- **Custody**: 201 public Lean sources — 104 STABLE-SURFACE, 96
  PUBLIC-EVIDENCE, 1 REPOSITORY-AGGREGATE — across eleven exact stable
  roots and 131 ownership relations (v13 baseline: 179/82/96/1, ten
  roots, 98). The PathVerdict substrate and the seven direct BreakGlass
  substrate inputs are intentionally multi-rooted.
- **Calculus root**: 191 exact receipts (rungs 2–7), fail-closed in
  `scripts/check-calculus-footprint.sh`; the rung-1 Domains/Located
  substrate is separately gated at 36 receipts in
  `scripts/check-pathverdict-footprint.sh`.
- **Rung-7 public axiom partition** (disjoint, gate-derived):
  101 = 3 axiom-free + 19 opaque-substrate-only + 4 `+propext` without
  `Quot.sound` + 67 `+Quot.sound` without `Classical.choice` + 8
  `+Classical.choice` (75 `Quot.sound`-bearing overall) — accepted
  explicitly at the rung-7 ratification. Rungs 1–6 receipts are all
  ≤ `propext`.
- **Description coherence**: a cross-repository six-site gate (research
  tree `scripts/check-calculus-descriptions.sh`) freezes the aggregate
  header, lakefile commentary, CI step, footprint-gate header, and the
  claim-register/readiness-ledger partition statements against the
  admitted state, including the ratified-name language.
- **Evidence custody**: the concrete seven-entry comparison ledger, the
  rung-6 ledger tether and audits, the 49-receipt BreakGlass hostile
  matrix, the legacy fixed-`Atoms` exploit, and every campaign packet
  remain research-tree custody, bound by seven ACTIVE
  normalized-source-equal extraction records per rung.

## What v14 does not claim

No runtime conformance, attestor honesty, origin-allocation uniqueness,
clock honesty, or cryptographic property; no closed inhabitant of the
abstract substrate; no discharge/payment lifecycle; no universal
completeness. The per-rung nonclaim fences in the readiness ledger and
claim register are part of the released surface. The plain-language
statement of the research program is
[`PLAIN-LANGUAGE-SUMMARY.md`](PLAIN-LANGUAGE-SUMMARY.md).

## Verification receipt (release preparation tree)

All by bare exit code, 2026-07-18, after the ratified-name doc sync and
version metadata flip:

- full battery per `AGENTS.md` — every build target, every footprint
  gate (incl. 191/191 Calculus and 36/36 PathVerdict), axiom and
  native_decide audits, Mathlib pin and closure, custody
  (201/104/96/1, 131), target gate (201/201), downstream consumer —
  pass
- cross-repository description-coherence gate — six sites coherent at
  rung 7 / 191 with the ratified-name language
- the operator performs the tag, GitHub release, and Zenodo deposit as
  separate acts; nothing in this ledger asserts them
