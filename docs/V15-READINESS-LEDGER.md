# V15 readiness ledger — Cross-Calculus Atlas

Date: 2026-07-22

Status: **local release candidate; not released**

V15 provides faithful cross-calculus mappings among GT, Execution Custody,
and Continuity Admission, preserving exact judgment indices, local
countermodels, and receipt-bound entitlement. It includes an exact-receipt
anti-minting result and a held-out partial StaticRole instance. It does not
establish a shared bridge algebra, generic frontier composition, generic
ownership, generic context transport, or a universal calculus.

This ledger is rooted at the operator-ratified public integration commit
`1f0e0208584e0f61fe49353dd0fc6b4775e22e00`, tree
`d2424b28a932c68027ec7bb0bbebd1e169221b99`, parent
`8113544cd7e8420d14b3f02c2325873aef2ac15b`. The final candidate commit,
tree, and parent are recorded in the separately committed verification receipt
and operator handoff, avoiding a self-referential Git object.

## Ratified local chain

| Gate | Commit | Tree | Parent |
| --- | --- | --- | --- |
| exact public transfer | `d1e2d18ffc6e27365ec890a6ae2439c87688b350` | `fbd5a31ec5e2432759db45d2359c3e3f74198b52` | `9dca58f4587a4a4f5b724662b176af8de3040c04` |
| transfer ratification record | `8bfa849693b3795b6c7236161baaa54c9f1f82f2` | `d47f0f779d05031e8ae61937cfb1e1b5e03800e2` | `d1e2d18ffc6e27365ec890a6ae2439c87688b350` |
| exact Continuity rename | `46e7a9aa5944fcc8826445c74ec08e1aa2dcb630` | `e27bc3174d3e9bd2d6f843d871a823c2b036674b` | `8bfa849693b3795b6c7236161baaa54c9f1f82f2` |
| dependency integration | `0b513fa184c12a10c685a6d13e45d085cd19499b` | `39ddfae2d420961cbe4809abe1ed1c3a4073e112` | `46e7a9aa5944fcc8826445c74ec08e1aa2dcb630` |
| Track A reconciliation | `05b4dff4df27bf69a9e3552498bc2ef92bed3242` | `8b2ebf8d9a8b715ce932e61d52e173f0d9f6f900` | `0b513fa184c12a10c685a6d13e45d085cd19499b` |
| cleanup and public index | `76d568a78d1611420ea765901ae679a9bc16ee84` | `3167a74fe0c08a24e14c8de5d87ff9a01f413201` | `05b4dff4df27bf69a9e3552498bc2ef92bed3242` |
| namespace-terminator correction | `8113544cd7e8420d14b3f02c2325873aef2ac15b` | `68ba6198a56d66c81592fdef882b2f9ff805c037` | `76d568a78d1611420ea765901ae679a9bc16ee84` |
| integration verification receipt | `1f0e0208584e0f61fe49353dd0fc6b4775e22e00` | `d2424b28a932c68027ec7bb0bbebd1e169221b99` | `8113544cd7e8420d14b3f02c2325873aef2ac15b` |
| qualification hostile audit | `247e5d002f40288c06452b9f6913ccb967c9655e` | `f0ff26c2a2bd0718096a1b3bd3b9363a30c1a704` | `1f0e0208584e0f61fe49353dd0fc6b4775e22e00` |
| release-candidate metadata | `df37e95d558035f91dcd0dbed48cf9f14fda5b28` | `83fdd97ee0f376a1e60b0836fc18593c82eec8e7` | `247e5d002f40288c06452b9f6913ccb967c9655e` |

## Source and campaign pins

- GT: source commit `71714265062e3b45092c4d79927dfe2ed77dc5fa`,
  tree `71cb93395a369ce4305288e15b55eb724da0814f`, ratified packet
  SHA-256 `203f1b54a02469160aee8771a109db77fb812b5bdecd0036c66d066db570d08a`.
- Execution Custody: public commit
  `9dca58f4587a4a4f5b724662b176af8de3040c04`, tree
  `7e2b27939bafe7a214085112af2777e395b1b94f`, source blob
  `5b4b8d00700e8aea2fbe5c94d17e99cdc933a876`, source SHA-256
  `966d1f6f63d022b13a1ff031fe0558c99e6b2b304ba6f89550d632de14d18aef`.
- Admissibility out-of-sample source: the same public commit and tree, blob
  `961f4d2a1ea7c5d9236338dedf42ded6481d1c3e`, SHA-256
  `13f0f8164ff6c9de6b9cfb05053fc1bed58aeb7d8c3f2289df5d69cb32dd5b7c`.
- Continuity historical candidate:
  `cc84f4b9a2bb85eda4942d13fb1696e3d44a45a3`, tree
  `661c7725fd16149155a460e47ab820149025d2d6`, parent
  `600c6f45b8dce82557e2efb99fc77ed234f8e9d5`; ratification
  `99f3973aca420817ac4eb5a5a1282252326c32e7`, tree
  `843c274726c6094320093e879d6d6288f8a32743`. The historical declaration
  manifest SHA-256 is
  `521c437be1d7f2ac93d0dfded7b368158a339cad8ee004ffb29d41120848c3b9`.
- StaticRole phase three: candidate
  `63367a9f488a7ecbaf369c929b4becfd3ad60022`, ratification
  `0dc621b782b0898152e325633cad1fbcb33b2f01`, ratification tree
  `f7ff0342aacfc4f0998ebacfd2c3b6b95b748b98`.
- PJ final Atlas: ratification
  `7be5a671276628d150c72e39ae43ff9a01e09085`, tree
  `ada9e0ab322378624627e784db25b35e706ff9d7`, parent
  `d07143a0b51dade3ebff4002ede7ac42523398ca`; final record SHA-256
  `3efad909f66b2caed45e57606c3c879ad877e902606d4046e057eff7942002aa`.

The private/public transfer manifest remains SHA-256
`05a29867a8c9c24996f9a1b975749a61379f32b5b8cdebc9a1100504147d6268`;
the normalized custody manifest remains SHA-256
`471ec4b52bdcb163dafa8eab671e5f26b9401351ff4da9908db0ab8e214b5e1d`.

## Continuity rename identity

`Someone` crossed to the single authoritative public implementation
`Continuity.Admission`. The correspondence manifest SHA-256 is
`3aafc4eceb0e96899772bb5824bbac3c999ede5e9355786982e3761a2071fabb`.
It covers 1,005 declarations and checks old/new fully qualified names,
normalized types, proof values, and axiom footprints. The claim remains
identity-bound continuity admission on the reachable fragment; it does not
establish authenticated identity, durable revocation, substrate rebinding,
retained route history, typed refusal, obligations, or operational-Continuity
correspondence.

## Track A freeze

Inquiry and Preparation remain byte-exact at private freeze commit
`cfeffc950e795752ad1928a314890185c0cda723`, tree
`4d9de55c0d19f3984dc486ac124b2e4f2a7e1e11`, custody closure
`de32412a7a29fbc98273c08747256ca9d319cfbd`. Six Lean blobs and three
boundary records reproduce. Their 102 theorems are independently scoped:
Inquiry 74 and Preparation 28; 83 are axiom-free and 19 use only `propext`.
They are comparison-only neighbors outside the frozen PJ primary surface.

## Compiled declaration and axiom footprint

`docs/V15-PUBLIC-DECLARATION-FOOTPRINT.json` is a deterministic census of
the V15-owned Continuity Admission, StaticRole, and PJ declaration surfaces.
Existing GT, Execution Custody, and Admissibility declarations retain their
separate public receipts.

| Surface | Declarations | Theorems | Axiom-free | `[propext]` |
| --- | ---: | ---: | ---: | ---: |
| Continuity Admission | 1,005 | 281 | 868 | 137 |
| StaticRole R0–R3 | 1,010 | 445 | 992 | 18 |
| PJ Atlas | 591 | 227 | 571 | 20 |
| **Total** | **2,606** | **953** | **2,431** | **175** |

The total contains zero `[Quot.sound]`, zero `[Classical.choice]`, and zero
mixed/other entries. These classifications are inherited; qualification did
not rewrite proofs to reduce them.

The hostile-fixture policy counts declarations in the Continuity hostile
qualification module, StaticRole `Countermodels` modules, and the exact PJ
hostile/boundary modules: 14 + 460 + 261 = **735 compiled declarations**.
The public hostile ledger directly maps the twelve required representative
collapse attacks to reproduced witnesses.

StaticRole remains exactly R0–R3 with no R4. PJ remains `ATLAS`, including
`FRONTIER-NOT-COMPOSITIONAL`, `NO-USEFUL-OWNERSHIP-COMMONALITY`,
`CONTEXT-TRANSPORT-NOT-GENERIC`, and
`ONLY-DOMAIN-SPECIFIC-RESIDUAL-THEORIES`.

## Candidate metadata and paths

The candidate version is `15.0.0` and the conservative title is
**V15 — Cross-Calculus Atlas**. `CITATION.cff` retains the concept DOI but
sets no release date and no unminted version DOI. The current published v14
tag and release remain unchanged: annotated tag object
`595b632f65b926d5430a2ff7ff031b502a26cfe0`, peeled commit
`ff491b808ebeab2a132d9ade46d234cf85dcfbe9`, tree
`72cba07e35588e9f67c252b0bd92cf0523ab178f`, version DOI
`10.5281/zenodo.21435270`, concept DOI `10.5281/zenodo.20369489`.

The complete campaign allowlist is
`docs/V15-RELEASE-CANDIDATE-PATHS.tsv`. No formal source, custody registry,
target registry, stable-root list, v14 surface, or generated custody aggregate
is changed by qualification.

## Qualification commands

The candidate receipt records the exit status of:

```text
lake build V15Integration
lake build V15IntegrationQualification
lake build CalculiStable CalculiScratch CalculiAll Calculi
python3 scripts/formalization_audit.py check --skip-external --skip-footprints
lake env lean <each of the seven V15 qualification leaves>
python3 scripts/check-v15-continuity-rename.py
python3 scripts/check-v15-integration.py
python3 scripts/check-v15-public-qualification.py
bash scripts/audit-axioms.sh
bash scripts/audit-native-decide.sh
bash scripts/check-mathlib-pin.sh
bash scripts/check-custody-classes.sh
bash scripts/check-mathlib-free-targets.sh
git diff --check
```

## Exact non-claims and remaining actions

V15 is not a shared bridge algebra, generic frontier composition law, generic
ownership theory, generic context transport, universal calculus, Planet,
Archipelago, complete theory of machine judgment, JCP implementation, or
operational AG/NQ realization. Receipt fibers and residual theories remain
local. StaticRole is a held-out faithful partial instance, not an R4 claim.

Only the operator may ratify the local candidate and later, in separately
authorized actions, push, tag, create a GitHub release, assign release dates,
mint a version DOI, or publish. **No push, tag, mint, publication, or release
occurred during this campaign.**
