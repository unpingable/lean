# PJ Tranche D-prime Verification Receipt

Date: 2026-07-22

## Result

`PJ-TRANCHE-D-PRIME-QUALIFICATION-PASS`

This receipt qualifies a hostile-audit and classification candidate. It does
not ratify Planet, Archipelago, Atlas, or Mirage.

## Exact continuation chain

| Object | Commit | Tree / parent |
|---|---|---|
| PJ-A candidate | `d634517fc08205758de59466c97f5998f774dabb` | tree `c539b62398d30b5d12a40fdffef53eb543305705`; parent `99f3973aca420817ac4eb5a5a1282252326c32e7` |
| PJ-A ratification | `d1fad6efc608b7daf3b8a8f47b7f4cfc5a1c249e` | tree `706da052cb2dcff572054f686884f92bb43829ad`; parent PJ-A candidate |
| PJ-B fast falsification | `a66918dda9dd32892d6275abaa59229633ab3a07` | tree `68d7023bfb42a8a08a490ad4419334ccd5b5ca92`; parent PJ-A ratification |
| PJ-B-prime candidate | `4e48186cc87249dd5e308e1381345d9758454687` | tree `8a7c6bf30da059dfe22e35750ae114fbb35eeccd`; parent PJ-B fast falsification |
| PJ-B-prime ratification | `06856876f7f111ad49a17b6eecba5b46ae238211` | tree `52c09c34aedaf2fcca2a193c0dfb1d82a7d5fa64`; parent PJ-B-prime candidate |
| PJ-C-prime candidate | `7bddca0411b1af93a76923691eb1d324a3f92856` | tree `6a97636eebdf1ddfd69a0572307d0e8b548b50d4`; parent PJ-B-prime ratification |
| PJ-C-prime ratification | `c2d011779ea1aa579cb199d5869b34b19b2180e6` | tree `5a8b5bb6d540c9ae777292d9a6ab02ac9f2dab07`; parent PJ-C-prime candidate |

## Source and declaration identities

- frozen PJ-A core SHA-256:
  `1d86bee97f92f2644d8605a05d6a31deaa3584f55582d4a09b638718ffff185c`;
- D-prime declaration manifest SHA-256:
  `5b4947101d4610fa86c536449e4eba399b601cf4c1b3cb396579d668b39f6e6a`;
- public Admissibility revision:
  `9dca58f4587a4a4f5b724662b176af8de3040c04`, tree
  `7e2b27939bafe7a214085112af2777e395b1b94f`;
- public Admissibility core blob:
  `961f4d2a1ea7c5d9236338dedf42ded6481d1c3e`, SHA-256
  `13f0f8164ff6c9de6b9cfb05053fc1bed58aeb7d8c3f2289df5d69cb32dd5b7c`.

The canonical declaration manifest includes this exact Admissibility source
pin alongside the four inherited PJ-A source pins. The declaration census
contains 591 PJ-owned declarations: 571 axiom-free and 20 exactly `[propext]`.
All 38 D-prime declarations and all 17 directly printed central receipts are
axiom-free.

## Commands and exact results

```text
python3 scripts/check-pj-tranche-d-prime.py --write-manifest
  PJ-TRANCHE-D-PRIME-QUALIFICATION-PASS
  591 compiled declarations
  17/17 direct receipts axiom-free

lake build LeanProofs.Admissibility.Calculus.Core
  PASS; 2 jobs; six public theorem receipts axiom-free

lake env lean PJ/Campaign/TrancheDPrimeQualification.lean
  PASS; 17/17 direct receipts axiom-free

lake build PJ
  PASS; 56 jobs

lake build CalculiStable CalculiScratch CalculiAll Calculi
  PASS; 269 jobs

python3 scripts/formalization_audit.py check --skip-external --skip-footprints
  FORMALIZATION AUDIT: PASS (19 checks)

git diff --check
  PASS
```

## Source line counts

- hostile-collapse executable: 184 lines;
- out-of-sample executable: 127 lines;
- qualification leaf: 27 lines;
- declaration dumper: 142 lines;
- fail-closed checker: 305 lines.

## Isolation

`PJ/Core.lean`, every ratified source calculus, every stable/default/public
aggregate, and the public repository remain unchanged. The public source is
imported only through the isolated PJ target. No generic frontier returned.
No JCP, AG/NQ integration, runtime work, public theory naming, push, tag,
mint, publication, or release occurred.
