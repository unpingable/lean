# PJ Tranche C-prime Verification Receipt

Date: 2026-07-22

## Result

`PJ-TRANCHE-C-PRIME-QUALIFICATION-PASS`

This receipt qualifies an isolated candidate. It does not ratify C-prime or
open D-prime.

## Exact continuation chain

| Object | Commit | Tree / parent |
|---|---|---|
| PJ-A candidate | `d634517fc08205758de59466c97f5998f774dabb` | tree `c539b62398d30b5d12a40fdffef53eb543305705`; parent `99f3973aca420817ac4eb5a5a1282252326c32e7` |
| PJ-A ratification | `d1fad6efc608b7daf3b8a8f47b7f4cfc5a1c249e` | tree `706da052cb2dcff572054f686884f92bb43829ad`; parent PJ-A candidate |
| PJ-B fast falsification | `a66918dda9dd32892d6275abaa59229633ab3a07` | tree `68d7023bfb42a8a08a490ad4419334ccd5b5ca92`; parent PJ-A ratification |
| PJ-B-prime candidate | `4e48186cc87249dd5e308e1381345d9758454687` | tree `8a7c6bf30da059dfe22e35750ae114fbb35eeccd`; parent PJ-B fast falsification |
| PJ-B-prime ratification | `06856876f7f111ad49a17b6eecba5b46ae238211` | tree `52c09c34aedaf2fcca2a193c0dfb1d82a7d5fa64`; parent PJ-B-prime candidate |

The frozen PJ-A core remains SHA-256
`1d86bee97f92f2644d8605a05d6a31deaa3584f55582d4a09b638718ffff185c`.
The rejected `PJ/TrancheB` executable surface remains absent.

## Source pins reused

- GT source custody: `71714265062e3b45092c4d79927dfe2ed77dc5fa`,
  tree `71cb93395a369ce4305288e15b55eb724da0814f`, packet
  `203f1b54a02469160aee8771a109db77fb812b5bdecd0036c66d066db570d08a`;
- Execution Custody: `9dca58f4587a4a4f5b724662b176af8de3040c04`,
  tree `7e2b27939bafe7a214085112af2777e395b1b94f`, source SHA-256
  `966d1f6f63d022b13a1ff031fe0558c99e6b2b304ba6f89550d632de14d18aef`;
- Someone source: `b00d76535ab6848eb2db80cb68601a07b118c4ef`,
  tree `8c7e42e8c97659763e5573d063a54fb1d5af1d45`;
- Someone qualification: `99f3973aca420817ac4eb5a5a1282252326c32e7`,
  tree `843c274726c6094320093e879d6d6288f8a32743`;
- StaticRole phase-three ratification:
  `0dc621b782b0898152e325633cad1fbcb33b2f01`, tree
  `f7ff0342aacfc4f0998ebacfd2c3b6b95b748b98`.

## Declaration and axiom result

- 553 compiled declarations across eleven selected modules;
- 533 axiom-free and 20 exactly `[propext]`;
- 39 C-prime compiled declarations, all axiom-free;
- 29/29 direct central receipts axiom-free;
- declaration manifest SHA-256
  `09c203d95157afb0ef379668f64753a9e74fb22c7e2387c8efde7c5e5d4821ab`.

## Commands and exact results

```text
python3 scripts/check-pj-tranche-c-prime.py --write-manifest
  PASS; 553 declarations; 29/29 central receipts axiom-free

lake env lean PJ/Campaign/TrancheCPrimeQualification.lean
  PASS; 29/29 direct receipts axiom-free

lake build PJ
  PASS; 53 jobs

lake build CalculiStable CalculiScratch CalculiAll Calculi
  PASS; 269 jobs

python3 scripts/formalization_audit.py check --skip-external --skip-footprints
  FORMALIZATION AUDIT: PASS (19 checks)

git diff --check
  PASS
```

The qualification leaf directly imports both C-prime modules, and the
declaration dumper directly imports all eleven selected modules. Source-code
checks reject executable generic-frontier identifiers after stripping comments
and strings.

## Isolation

No source calculus, stable/default/public aggregate, sibling repository,
runtime, JCP surface, release object, public theory name, tag, mint,
publication, or remote changed.
