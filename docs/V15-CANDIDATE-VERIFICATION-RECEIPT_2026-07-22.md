# V15 local release-candidate verification receipt

Date: 2026-07-22

Disposition: `READY-FOR-V15-OPERATOR-RATIFICATION`

The hostile public qualification reproduces the ratified formal object and
prepares version `15.0.0` as a local candidate titled **V15 — Cross-Calculus
Atlas**. V15 remains a faithful atlas with exact local receipts and
countermodels, not a shared bridge algebra or universal calculus.

No push, tag, mint, publication, release, remote configuration, remote-branch
change, stable-root promotion, or v14 surface change occurred.

## Qualification base and local commits

The exact operator-ratified integration base is commit
`1f0e0208584e0f61fe49353dd0fc6b4775e22e00`, tree
`d2424b28a932c68027ec7bb0bbebd1e169221b99`, parent
`8113544cd7e8420d14b3f02c2325873aef2ac15b`.

| Gate | Commit | Tree | Parent | Exact paths |
| --- | --- | --- | --- | --- |
| bounded public-claim and hostile audit | `247e5d002f40288c06452b9f6913ccb967c9655e` | `f0ff26c2a2bd0718096a1b3bd3b9363a30c1a704` | `1f0e0208584e0f61fe49353dd0fc6b4775e22e00` | `README.md`; `docs/V15-PUBLIC-HOSTILE-AUDIT_2026-07-22.md` |
| release-candidate metadata | `df37e95d558035f91dcd0dbed48cf9f14fda5b28` | `83fdd97ee0f376a1e60b0836fc18593c82eec8e7` | `247e5d002f40288c06452b9f6913ccb967c9655e` | `CHANGELOG.md`; `CITATION.cff`; `README.md`; `docs/V15-DOI-PREPARATION.md`; `docs/V15-RELEASE-CANDIDATE.md`; `lakefile.toml` |
| readiness ledger and manifests | `4c4e53443f0c351db28c7342191f4ffc9c0f6b4a` | `647530cb184ee7e542651821dcc611d5de738e47` | `df37e95d558035f91dcd0dbed48cf9f14fda5b28` | `docs/V15-PUBLIC-DECLARATION-FOOTPRINT.json`; `docs/V15-READINESS-LEDGER.md`; `docs/V15-RELEASE-CANDIDATE-PATHS.tsv`; `scripts/check-v15-public-qualification.py` |

This receipt is the sole path in the final verification commit. That commit's
identity is recorded in the operator handoff because a Git object cannot
contain its own hash. Its exact parent is
`4c4e53443f0c351db28c7342191f4ffc9c0f6b4a`.

## Source fidelity and scientific result

- GT remains pinned to source commit
  `71714265062e3b45092c4d79927dfe2ed77dc5fa`, tree
  `71cb93395a369ce4305288e15b55eb724da0814f`, packet SHA-256
  `203f1b54a02469160aee8771a109db77fb812b5bdecd0036c66d066db570d08a`.
- Execution Custody and the Admissibility out-of-sample source remain exact at
  public commit `9dca58f4587a4a4f5b724662b176af8de3040c04`, tree
  `7e2b27939bafe7a214085112af2777e395b1b94f`; their source SHA-256 values
  remain `966d1f6f63d022b13a1ff031fe0558c99e6b2b304ba6f89550d632de14d18aef`
  and `13f0f8164ff6c9de6b9cfb05053fc1bed58aeb7d8c3f2289df5d69cb32dd5b7c`.
- The Continuity checker reproduces all 1,005 historical-to-public
  declarations with type, proof-value, and axiom identity under only the exact
  namespace rename. There is no duplicate authoritative `Someone` source.
- The six Track A Lean blobs and three boundary records remain exact at freeze
  commit `cfeffc950e795752ad1928a314890185c0cda723`, tree
  `4d9de55c0d19f3984dc486ac124b2e4f2a7e1e11`. Inquiry and Preparation remain
  independent comparison-only neighbors.
- StaticRole remains R0–R3 at phase-three candidate
  `63367a9f488a7ecbaf369c929b4becfd3ad60022`, ratification
  `0dc621b782b0898152e325633cad1fbcb33b2f01`, tree
  `f7ff0342aacfc4f0998ebacfd2c3b6b95b748b98`. No R4 path exists.
- The four PJ manifests reproduce 1,950 cumulative declarations and 74
  cumulative axiom-bearing entries. The final operator record remains
  SHA-256
  `3efad909f66b2caed45e57606c3c879ad877e902606d4046e057eff7942002aa`
  and says `RATIFY-PJ-D: ATLAS`.

The authoritative negative results remain
`FRONTIER-NOT-COMPOSITIONAL`, `NO-USEFUL-OWNERSHIP-COMMONALITY`,
`CONTEXT-TRANSPORT-NOT-GENERIC`, and
`ONLY-DOMAIN-SPECIFIC-RESIDUAL-THEORIES`. No rejected frontier module was
restored.

## Hostile qualification

The twelve requested attacks reproduce: bridge/target inhabitant without
receipt; target truth without entitlement; wrong subject, context, and bridge
receipts; frontier projection; owner as an empty label; trivial identity
context transport; StaticRole wrong wiring; Continuity same-name without
admission; Execution attempt without commit; and GT projection without
runtime correspondence. The exact witness map is in
`docs/V15-PUBLIC-HOSTILE-AUDIT_2026-07-22.md`.

The compiled hostile-module census is 735 declarations: 14 Continuity, 460
StaticRole, and 261 PJ. The qualification also reproduces the positive
collapse controls showing why anti-minting remains exact and adapter-local.

## Declaration and axiom census

| Surface | Declarations | Theorems | Axiom-free | `[propext]` |
| --- | ---: | ---: | ---: | ---: |
| Continuity Admission | 1,005 | 281 | 868 | 137 |
| StaticRole R0–R3 | 1,010 | 445 | 992 | 18 |
| PJ Atlas | 591 | 227 | 571 | 20 |
| **V15-owned total** | **2,606** | **953** | **2,431** | **175** |

The V15-owned total has zero `[Quot.sound]`, zero `[Classical.choice]`, and
zero mixed/other entries. The separately frozen Track A surface has 102
theorems: 83 axiom-free and 19 `[propext]`. The repository-wide classifier
also reports 23 signature axioms, zero interface-law axioms, eight specimens,
zero forbidden, and zero unclassified declarations.

## Verification results

Every bare command exited zero:

```text
/home/jbeck/git/lean$ lake build V15Integration
  Build completed successfully (60 jobs).
/home/jbeck/git/lean$ lake build V15IntegrationQualification
  Build completed successfully (70 jobs).
/home/jbeck/git/skunkworks/formalization$ lake build CalculiStable CalculiScratch CalculiAll Calculi
  Build completed successfully (269 jobs).
/home/jbeck/git/skunkworks/formalization$ python3 scripts/formalization_audit.py check --skip-external --skip-footprints
  FORMALIZATION AUDIT: PASS (19 checks)
```

All seven direct leaves passed:

```text
lake env lean formalization/Continuity/Admission/Qualification/Campaign.lean
lake env lean formalization/StaticRole/Campaign/Qualification.lean
lake env lean formalization/StaticRole/Campaign/PhaseThreeQualification.lean
lake env lean formalization/PJ/Campaign/TrancheAQualification.lean
lake env lean formalization/PJ/Campaign/TrancheBPrimeQualification.lean
lake env lean formalization/PJ/Campaign/TrancheCPrimeQualification.lean
lake env lean formalization/PJ/Campaign/TrancheDPrimeQualification.lean
```

The public checkers report:

- Continuity: 1,005 declarations preserve type, value, and axiom identity;
- integration: source pins, Track A, four PJ manifests, and `ATLAS` pass;
- qualification: 2,606 declarations, 953 theorems, 735 hostile declarations,
  and twelve representative collapses pass;
- custody: 273/273 public Lean sources, comprising 115 stable, 157 evidence,
  and one aggregate source across twelve stable roots;
- targets/dependencies: 28 registered public targets and 273/273 source
  ownership, with Mathlib-reaching targets explicit-only;
- axiom classifier: zero forbidden and zero unclassified declarations;
- native-decision audit: six allowed finite-witness occurrences;
- Mathlib pin: lakefile and manifest both pin
  `6ef8cc2731780be866bf243afcb7732f4da5f406`;
- `git diff --check`: pass.

## Candidate manifests and metadata

| Artifact | SHA-256 |
| --- | --- |
| private/public transfer manifest | `05a29867a8c9c24996f9a1b975749a61379f32b5b8cdebc9a1100504147d6268` |
| normalized public-custody manifest | `471ec4b52bdcb163dafa8eab671e5f26b9401351ff4da9908db0ab8e214b5e1d` |
| Continuity correspondence | `3aafc4eceb0e96899772bb5824bbac3c999ede5e9355786982e3761a2071fabb` |
| compiled declaration footprint | `94112eb540a6537620d2617c8151053c524d9f0986d823ef7029783c425e7397` |
| candidate changed-path manifest | `d3e0603962b81e4134f098efc00d0d5e72fc29e78a90ac29b6669d46d0f4ab86` |
| readiness ledger | `8efa5e77e42cf3a9770301537699e62a56776c35ffb18bdd68c1727af667f966` |
| qualification checker | `203287e4d03285f3e1fc002b4f198f5d7df613f0528147e55b2181fc2bc39fe1` |

Metadata changes are limited to the candidate version, conservative Atlas
title and abstract, README/version index, candidate changelog and version
page, DOI preparation record, and readiness records. `CITATION.cff` retains
only the existing concept DOI and has no release date or unminted version DOI.
No tag or release object changed.

## Exact claim and non-claims

V15 provides faithful cross-calculus mappings among GT, Execution Custody,
and Continuity Admission, preserving exact judgment indices, local
countermodels, and receipt-bound entitlement. It includes an exact-receipt
anti-minting result and a held-out partial StaticRole instance.

It does not establish a shared bridge algebra, generic frontier composition,
generic ownership, generic context transport, universal calculus, Planet,
Archipelago, complete theory of machine judgment, JCP implementation, or
operational AG/NQ realization. Exact entitlement requires local qualified
receipts; receipt fibers and residual theories remain domain-specific.

The remaining actions are operator ratification and, only under later
separate authorization, push, tag, GitHub release, release-date assignment,
version-DOI mint, and publication. **No push, tag, mint, publication, or
release occurred.**
