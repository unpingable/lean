# PJ Tranche-A Verification Receipt

Date: 2026-07-22

## Result

`PJ-TRANCHE-A-QUALIFICATION-PASS`

This receipt qualifies the provisional PJ-A candidate as an isolated research
surface. It does not ratify a shared theory, open Tranche B, or choose among
Planet, Archipelago, Atlas, and Mirage.

## Frozen source inputs

| Source | Revision | Tree / exact identity |
|---|---|---|
| Governed Transport source custody | `71714265062e3b45092c4d79927dfe2ed77dc5fa` | tree `71cb93395a369ce4305288e15b55eb724da0814f`; packet SHA-256 `203f1b54a02469160aee8771a109db77fb812b5bdecd0036c66d066db570d08a` |
| Execution Custody public source | `9dca58f4587a4a4f5b724662b176af8de3040c04` | tree `7e2b27939bafe7a214085112af2777e395b1b94f`; blob `5b4b8d00700e8aea2fbe5c94d17e99cdc933a876`; SHA-256 `966d1f6f63d022b13a1ff031fe0558c99e6b2b304ba6f89550d632de14d18aef` |
| Someone source | `b00d76535ab6848eb2db80cb68601a07b118c4ef` | tree `8c7e42e8c97659763e5573d063a54fb1d5af1d45`; blob `80a71ce18e55515a97567cc9d9f162fd23998ff7` |
| Someone qualification | `99f3973aca420817ac4eb5a5a1282252326c32e7` | tree `843c274726c6094320093e879d6d6288f8a32743` |
| StaticRole held-out source | `0dc621b782b0898152e325633cad1fbcb33b2f01` | tree `f7ff0342aacfc4f0998ebacfd2c3b6b95b748b98` |

All pinned commits, trees, source blobs, worktree bytes, and relevant clean
paths reproduced. The GT file inventory was read from the single
digest-pinned canonical `source-blobs.tsv`; the PJ checker does not contain a
second copied inventory.

## Exact PJ footprint

- frozen `PJ/Core.lean` SHA-256:
  `1d86bee97f92f2644d8605a05d6a31deaa3584f55582d4a09b638718ffff185c`;
- compiled owned declarations: 292;
- compiled declaration kinds: 147 definitions, 112 theorems, 11 inductives,
  11 constructors, and 11 recursors;
- compiled axiom footprint: 278 axiom-free and 14 exactly `[propext]`;
- `Quot.sound`: zero;
- `Classical.choice`: zero;
- other or mixed footprints: zero;
- direct central receipts: 70;
- direct central receipt footprint: 63 axiom-free and seven exactly
  `[propext]`;
- declaration-manifest SHA-256:
  `be2b092ed2e08e948858e7d7a6ae77893b1baf36b6d95cb58050401cfbe2955a`.

The `[propext]` footprint is inherited only through exact Someone
preservation and anti-entitlement contact. PJ introduces no new axiom class.

## Source line census

| Surface | Lines |
|---|---:|
| `PJ/Core.lean` | 58 |
| `PJ/Hostile.lean` | 69 |
| Governed Transport adapter | 225 |
| Execution Custody adapter | 308 |
| Someone Continuity adapter | 143 |
| held-out StaticRole adapter | 388 |
| direct qualification leaf | 83 |
| declaration dumper | 127 |
| qualification checker | 860 |
| isolated aggregate | 14 |

The checker is scientific qualification infrastructure, not a custody-chain
verifier. Any later candidate/ratification ancestry check remains the job of
the repository's generic `scripts/verify-governed-revision.py` mechanism.

## Commands and exact results

```text
python3 scripts/check-pj-tranche-a.py
  PASS; PJCrossCalculus 41 jobs
  292 compiled declarations
  70 direct axiom receipts

lake env lean PJ/Campaign/TrancheAQualification.lean
  PASS; 70/70 receipts reproduced

lake build CalculiStable CalculiScratch CalculiAll Calculi
  PASS; 269 jobs

python3 scripts/formalization_audit.py check --skip-external --skip-footprints
  FORMALIZATION AUDIT: PASS (19 checks)

git diff --check
  PASS

python3 scripts/check-pj-tranche-a.py --skip-build
  PASS; serialized manifest and source pins exact
```

The normal checker, explicit manifest-regeneration comparison, and
metadata-only checker modes also reproduced the same canonical manifest.

## Isolation result

- `PJCrossCalculus` remains a non-default target;
- PJ is absent from `Calculi`, `CalculiAll`, `CalculiStable`, and
  `CalculiScratch`;
- no source calculus was edited;
- no operational repository was integrated;
- no public module, release metadata, custody aggregate, tag, or transfer was
  created;
- unrelated sibling work remained unstaged and untouched.
