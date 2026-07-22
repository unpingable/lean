# V15 Public Transfer Verification Receipt

Date: 2026-07-22

Disposition: `READY-FOR-V15-PUBLIC-TRANSFER-RATIFICATION`

## Authorized public-custody result

The revised campaign authorization separates frozen private-source identity,
required public-custody identity, and normalized semantic-body identity. All
56 transferred Lean files now carry the required public custody header; all
56 paths and both isolated targets are registered without changing or
weakening either public checker.

The exact custody operation and normalization are recorded in
`docs/V15-PUBLIC-CUSTODY-TRANSFORMATION_2026-07-22.md`. The frozen private
source manifest is unchanged. The normalized manifest proves that removing
only the inserted custody metadata restores every pre-custody public body,
with the same three separately recorded GT import/namespace adjustments.

This receipt records a bounded, release-neutral transfer. It does not promote
any stable surface, amend a release aggregate, rename Someone, open StaticRole
R4, push, tag, mint, publish, or release.

## Initial public state

| Field | Exact value |
| --- | --- |
| branch | `main` |
| commit | `9dca58f4587a4a4f5b724662b176af8de3040c04` |
| tree | `7e2b27939bafe7a214085112af2777e395b1b94f` |
| version | `14.0.0` (`v14.0.0-10-g9dca58f`) |
| worktree and index | clean |
| unrelated public work | none |
| active build processes | none |
| transfer branch | `v15-public-transfer-candidate` |

Before the authorized custody edit, the preserved candidate contained exactly
131 staged paths, no unstaged work, and staged-diff SHA-256
`c8b2795c18f6028c0d518396d26368bca93fbaa230e6150e514b63176a1210bf`.
The frozen transfer-manifest SHA-256 was already
`05a29867a8c9c24996f9a1b975749a61379f32b5b8cdebc9a1100504147d6268`.
No staged path was discarded, reset, or reconstructed.

The private source worktree had pre-existing unrelated untracked material and
a tracked `README.md` modification. None was read as campaign authority,
modified, staged, or transferred. All extraction used fixed Git objects.

The private v15 Track A gate reproduced 6/6 Lean blobs and 3/3 boundary
records at endpoint `cfeffc950e795752ad1928a314890185c0cda723` and custody
closure `de32412a7a29fbc98273c08747256ca9d319cfbd`.

## Authoritative objects

- Final PJ ratification: commit
  `7be5a671276628d150c72e39ae43ff9a01e09085`, tree
  `ada9e0ab322378624627e784db25b35e706ff9d7`, parent
  `d07143a0b51dade3ebff4002ede7ac42523398ca`. The final operator record
  SHA-256 is
  `3efad909f66b2caed45e57606c3c879ad877e902606d4046e057eff7942002aa`.
- Someone qualification candidate: commit
  `cc84f4b9a2bb85eda4942d13fb1696e3d44a45a3`, tree
  `661c7725fd16149155a460e47ab820149025d2d6`, parent
  `600c6f45b8dce82557e2efb99fc77ed234f8e9d5`. Its exact subsequent
  `RATIFY-SOMEONE-CONTINUITY` object is commit
  `99f3973aca420817ac4eb5a5a1282252326c32e7`, tree
  `843c274726c6094320093e879d6d6288f8a32743`, directly parented by the
  candidate. The declaration-manifest digest is
  `521c437be1d7f2ac93d0dfded7b368158a339cad8ee004ffb29d41120848c3b9`.
- StaticRole phase-three ratification: commit
  `0dc621b782b0898152e325633cad1fbcb33b2f01`, tree
  `f7ff0342aacfc4f0998ebacfd2c3b6b95b748b98`, directly parented by
  candidate `63367a9f488a7ecbaf369c929b4becfd3ad60022`.
- PJ-A, PJ-B fast falsification, PJ-B-prime, and PJ-C-prime candidate and
  ratification commits, trees, and parent chains matched the fixed campaign
  pins in the transfer instruction and campaign manifests.

## Existing public source pins

- GT: all 13 mapped public leaves reproduce the ratified packet mapping for
  source commit `71714265062e3b45092c4d79927dfe2ed77dc5fa`, tree
  `71cb93395a369ce4305288e15b55eb724da0814f`, packet digest
  `203f1b54a02469160aee8771a109db77fb812b5bdecd0036c66d066db570d08a`.
- Execution Custody: public revision
  `9dca58f4587a4a4f5b724662b176af8de3040c04`, tree
  `7e2b27939bafe7a214085112af2777e395b1b94f`, blob
  `5b4b8d00700e8aea2fbe5c94d17e99cdc933a876`, SHA-256
  `966d1f6f63d022b13a1ff031fe0558c99e6b2b304ba6f89550d632de14d18aef`.
- Admissibility core: the same public revision and tree, blob
  `961f4d2a1ea7c5d9236338dedf42ded6481d1c3e`, SHA-256
  `13f0f8164ff6c9de6b9cfb05053fc1bed58aeb7d8c3f2289df5d69cb32dd5b7c`.

No public source pin mismatch was found.

## Transfer exactness

The machine-readable path ledger is
`docs/V15-PUBLIC-TRANSFER-MANIFEST.tsv`, SHA-256
`05a29867a8c9c24996f9a1b975749a61379f32b5b8cdebc9a1100504147d6268`.
It contains 129 data rows: 128 extracted private paths plus the isolated
public `lakefile.toml` target adjustment. At the frozen pre-custody layer,
125 extracted paths are byte-identical and three have only the unavoidable
public GT module-address and namespace alpha substitution:

1. `formalization/PJ/Instances/GovernedTransport.lean`;
2. `formalization/PJ/TrancheBPrime/Instances.lean`;
3. `formalization/PJ/TrancheCPrime/ContextTransport.lean`.

For each of those three files, mechanically applying the packet-authorized mapping
`Calculi.Scratch.GovernedTransport` to `LeanProofs.GovernedTransport`, plus
the physical hostile-module import address
`LeanProofs.GovernedTransportEvidence.Hostile`, reconstructs the normalized
public body exactly.

The public-custody layer is recorded separately in
`docs/V15-PUBLIC-CUSTODY-NORMALIZED-BODY-MANIFEST.tsv`, SHA-256
`471ec4b52bdcb163dafa8eab671e5f26b9401351ff4da9908db0ab8e214b5e1d`.
It contains exactly 56 Lean rows. Every public full-file digest differs by the
required custody metadata, while every normalized body digest equals its
frozen pre-custody destination digest. Declaration names, theorem statement
text, proof bodies, countermodels, and printed axiom receipts are unchanged.
The seven public qualification leaves emit axiom lines byte-for-byte equal to
the private leaves.

Someone remains at `someone/Someone.lean` in namespace `Someone`.
StaticRole contains R0 through R3 and no R4 path. The rejected exploratory
`formalization/PJ/TrancheB/` directory is absent.

## Verification

The following bare commands exited zero in the repository that owns each
target or audit:

```text
/home/jbeck/git/skunkworks/formalization$ lake build CalculiStable CalculiScratch CalculiAll Calculi
/home/jbeck/git/skunkworks/formalization$ lake build SomeoneContinuityQualification StaticRole PJCrossCalculus
/home/jbeck/git/skunkworks/formalization$ python3 scripts/formalization_audit.py check --skip-external --skip-footprints
/home/jbeck/git/lean$ lake build V15PublicTransfer
/home/jbeck/git/lean$ lake build V15SomeoneSources
/home/jbeck/git/lean$ lake build
/home/jbeck/git/lean$ bash scripts/audit-axioms.sh
/home/jbeck/git/lean$ python3 scripts/check-v15-public-transfer.py
/home/jbeck/git/lean$ scripts/check-custody-classes.sh
/home/jbeck/git/lean$ scripts/check-mathlib-free-targets.sh
/home/jbeck/git/lean$ git diff --check
```

The formalization audit passed 19 checks. The `Calculi*` targets and
`scripts/formalization_audit.py` are source-repository facilities and do not
exist in the public package, so they were run in their owning fixed private
worktree; unrelated private work was not touched.

All seven qualification leaves were also run directly in both environments:

- Someone: 21 central receipts;
- StaticRole phase two: 48 central receipts;
- StaticRole phase three: 32 central receipts;
- PJ-A: 70 central receipts;
- PJ-B-prime: 32 central receipts;
- PJ-C-prime: 29 central receipts;
- PJ-D-prime: 17 central receipts.

Every public axiom line matched its private counterpart. Revision-bound
manifest checks passed at the PJ-A, PJ-B-prime, PJ-C-prime, and PJ-D-prime
candidate commits, covering respectively 292, 514, 553, and 591 compiled
declarations. The Someone checker reproduced 1,005 declarations: 868
axiom-free and 137 exactly `[propext]`.

The final gates also verified every transfer-ledger private source digest,
every public full-file and normalized-body digest, every source commit/tree
pin, all campaign-manifest bytes, the unchanged 16-file public GT target
surface including its Identity/evidence split, absence of the rejected
frontier directory, absence of an R4 surface, historical Someone naming,
273/273 public custody and target ownership, and `git diff --check`.

## Preserved scientific classification

The transferred record retains:

- `FRONTIER-NOT-COMPOSITIONAL`;
- exact-receipt anti-minting;
- `NO-USEFUL-OWNERSHIP-COMMONALITY`;
- `CONTEXT-TRANSPORT-NOT-GENERIC`;
- `ONLY-DOMAIN-SPECIFIC-RESIDUAL-THEORIES`;
- the held-out StaticRole faithful partial instance;
- the out-of-sample Admissibility faithful partial instance;
- every hostile-collapse finding; and
- final classification `ATLAS`.

PJ is a faithful cross-calculus atlas, not a shared algebra or universal
calculus. No Archipelago, Planet, shared-algebra, or universal-calculus claim
is made.
