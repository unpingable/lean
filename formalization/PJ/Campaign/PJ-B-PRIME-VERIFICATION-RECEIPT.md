# PJ Tranche B-prime Verification Receipt

Date: 2026-07-22

## Result

`PJ-TRANCHE-B-PRIME-QUALIFICATION-PASS`

This receipt qualifies an isolated candidate. It does not ratify B-prime,
open C-prime, restore generic frontier composition, or choose a final PJ
classification.

## Frozen inputs

| Object | Revision | Tree / identity |
|---|---|---|
| PJ-A candidate | `d634517fc08205758de59466c97f5998f774dabb` | `c539b62398d30b5d12a40fdffef53eb543305705` |
| PJ-A ratification | `d1fad6efc608b7daf3b8a8f47b7f4cfc5a1c249e` | `706da052cb2dcff572054f686884f92bb43829ad` |
| PJ-B fast falsification | `a66918dda9dd32892d6275abaa59229633ab3a07` | `68d7023bfb42a8a08a490ad4419334ccd5b5ca92` |
| GT source custody | `71714265062e3b45092c4d79927dfe2ed77dc5fa` | `71cb93395a369ce4305288e15b55eb724da0814f`; packet `203f1b54a02469160aee8771a109db77fb812b5bdecd0036c66d066db570d08a` |
| Execution Custody public source | `9dca58f4587a4a4f5b724662b176af8de3040c04` | `7e2b27939bafe7a214085112af2777e395b1b94f`; source SHA-256 `966d1f6f63d022b13a1ff031fe0558c99e6b2b304ba6f89550d632de14d18aef` |
| Someone source | `b00d76535ab6848eb2db80cb68601a07b118c4ef` | `8c7e42e8c97659763e5573d063a54fb1d5af1d45` |
| Someone qualification | `99f3973aca420817ac4eb5a5a1282252326c32e7` | `843c274726c6094320093e879d6d6288f8a32743` |
| StaticRole ratification | `0dc621b782b0898152e325633cad1fbcb33b2f01` | `f7ff0342aacfc4f0998ebacfd2c3b6b95b748b98` |

The frozen PJ-A core remained byte-exact at SHA-256
`1d86bee97f92f2644d8605a05d6a31deaa3584f55582d4a09b638718ffff185c`.

## Declaration and axiom footprint

- 514 compiled owned PJ declarations across nine exact modules;
- 494 axiom-free;
- 20 exactly `[propext]`;
- zero `Quot.sound`, `Classical.choice`, other, or mixed footprints;
- 222 compiled declarations in the three B-prime modules;
- B-prime module footprint: 216 axiom-free and six generated structure
  `mk.injEq` declarations exactly `[propext]`;
- 32 named central receipts, all axiom-free;
- declaration-manifest SHA-256:
  `c7544b561271ca64f0c15d8f7c9a980b7cf7eb3da8ce020f0aece3c3aebfebc4`.

## Source line census

| Surface | Lines |
|---|---:|
| anti-minting core and hostile fixtures | 320 |
| primary instance specializations | 280 |
| held-out StaticRole specialization | 63 |
| direct qualification leaf | 48 |
| deterministic declaration dumper | 134 |
| fail-closed B-prime checker | 228 |
| isolated PJ aggregate | 18 |

## Commands and exact results

```text
python3 scripts/check-pj-tranche-b-prime.py --write-manifest
  PASS; isolated target and source pins exact
  514 compiled declarations; 32/32 central receipts axiom-free

lake env lean PJ/Campaign/TrancheBPrimeQualification.lean
  PASS; 32/32 direct receipts axiom-free

lake build PJ
  PASS; 43 jobs

lake build CalculiStable CalculiScratch CalculiAll Calculi
  PASS; 269 jobs

python3 scripts/formalization_audit.py check --skip-external --skip-footprints
  FORMALIZATION AUDIT: PASS (19 checks)
```

The qualification leaf imports the exact B-prime modules directly. The
declaration dumper imports all nine selected modules directly. Neither can
silently rely on a stale `PJ` aggregate object.

## Isolation

PJ remains a non-default target. No source calculus, default/stable/public
aggregate, sibling repository, runtime, JCP surface, release object, or
public theory name changed.
