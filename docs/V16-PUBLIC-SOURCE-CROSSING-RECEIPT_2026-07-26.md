# V16 governed-transition boundaries — public source-crossing receipt

Candidate published 2026-07-26; not released, not stable, and not V16 final.

## Identity pins

| Field | Exact value |
| --- | --- |
| private repository | `unpingable/skunkworks` |
| private local/tracking/live start | `b3d73a7a8f3c47486a29767b8b28c809af0f4e57` |
| public local/tracking/live start | `69bdc032dc00db1e750ffc6fdc9f73a8cdcbbf81` |
| extracted `LeanProofs` tree | `84f209f57e2495463833137cd58aac7ce73e6f96` |
| extracted source snapshot pin | `f7b32f61cfd11b9bb6cafd1cf3674ddebface558` |
| public source/wiring endpoint before this receipt | `160a97ffb17ae3c7cd1f69ffce61268ee17074ef` |
| crossing date | `2026-07-26` |

Both repositories began on `main` with clean worktrees and equal local,
tracking, and live identities. The public final remote identity is recorded
after the fast-forward push in the bounded private post-crossing receipt; a
commit cannot contain its own object ID.

## Authorized Lean source

| Public destination | Extracted SHA-256 | Extracted Git blob | Public SHA-256 | Public Git blob |
| --- | --- | --- | --- | --- |
| `LeanProofs/GovernedTransitionBoundaries.lean` | `db9ffcb21ad439b8d15b96aa1316e608a199d785973139565afd65d30056418c` | `9b2dba4ea230eafb842eba5818e1bb0568dfae56` | `62e53c24c70dd7d4d2085d6163a7f31f6cc8abfe80a391cc81924bdb2a6621c7` | `4d609e83bcdf4997b313cc5980ce93f4f237fd40` |
| `LeanProofs/GovernedTransitionBoundaries/Core.lean` | `eb10cbca6b672ebea0f380880dc189bc633aafa8bb635aec7b9c33a7320e261b` | `c40891d11cf00d5480f5bea5376f1dbc4d020f6d` | `00834c3a7421b09c819e70b90b45d487d5fe434a92e4096dea571b0342eca045` | `25f8b2c3c3520e15167bc0e181766ff425c14a4e` |
| `LeanProofs/GovernedTransitionBoundariesEvidence.lean` | `226de883b8017a7f479be445e0bef21206d187298c7e076d7331da81587d96b9` | `a28fedc36d97ce826a9d9179d51c3f1e12881f30` | `fe15e20648975f9c178fbfee4fa31c5d6278e904e697dd619e66c0aa70468f4c` | `ccc559636705359e6a66614f5e1d4397954289d8` |
| `LeanProofs/GovernedTransitionBoundariesEvidence/ContextBoundary.lean` | `2d29747422d8d6b1e9c57309be096f756981de6fe0cfe450084f426cf94e0a9f` | `7a902d1858c315572336967c8657f76f87131f03` | `387804a105af1cb2f81bde19b684ebfadd0419278902c863a28015ff6c797ebc` | `c48156ed1bbf56c498ab340cf992a3219c380566` |
| `LeanProofs/GovernedTransitionBoundariesEvidence/FiniteRepresentation.lean` | `a05b753aa28b647003d753ca5c09d2ffa26b6ef13a11276d8943c94cc496d371` | `cf517323a8a3d4cd325c8ba07349fba3acbe3f7d` | `74bc37f47b1cd5db7414c8f031d225c1433b3e79e6d0009726de654f0599e8ce` | `f7aa71b443b381daccbe5b28998f93cfc04d36c5` |
| `LeanProofs/GovernedTransitionBoundariesEvidence/GroundingBoundary.lean` | `6991a2ba4de6bdab517a7efffea91bbdcd900cdcc24a34100ef198f58bda1e9a` | `216119cd7267ad7641d3062288c027a7bae0423d` | `a2fe9a14375b9f90051054b0a411c247e263211254906a811b215306c73f115e` | `ba26fccf111ee19be716d2def936906d461fb0b4` |
| `LeanProofs/GovernedTransitionBoundariesEvidence/HistoricalBoundary.lean` | `d07cc38cace4d1b09076421622978bfff4a3bad46af78609aa60305a40d9fe4d` | `d0ad9d4430390b329ec4e300340ff901c1bd1340` | `2415933395742349b542a3fd0f166555e61d976fcc1ac289f07ab2070b7b9b5b` | `b6a4a84df2f11ee64ceaaf75c152c9fafea1ac6e` |
| `LeanProofs/GovernedTransitionBoundariesEvidence/JurisdictionBoundary.lean` | `f5817f4b6a77d41f5c9609e16e11953d869739194bb6a41c76f9ab40cab1e4b3` | `456b17ce08d07561d950c1c13cc3d93c74beb88e` | `e2b4e225357be36e1a000be7e0123aceca193d66ab320f804a2502025c66e1f8` | `885bd3caa65cce4c1ab82837501272afe49de9d4` |
| `LeanProofs/GovernedTransitionBoundariesEvidence/Qualification.lean` | `ce7d44e9ee23c830f4afa5f46348072d4e992823e4228dc92a69fce0326eda97` | `4d747b2f722ab5a56a1d3b816cec5c3732e2f925` | `4cfd8e51fff863b66f112ca5453fe86be2b2f194f4416232e4cf8ee2b487b92c` | `a7770f1a69ab3b9a8bac255f585e70a838d3c559` |
| `LeanProofs/GovernedTransitionBoundariesEvidence/RealizabilityBoundary.lean` | `6fa9e29ded25b5ef6cfbfab9460bfa50fed97bf5ac72d3ff0ae4728d08404dc4` | `695ff036e8208d74657bb0971ffe17ca4ed20947` | `a9da012d44e61caaa6e01f44a96e5efbf6d7496c5bddef3019bf54498a3db810` | `8a5d94126f74ace3bf0a1b7db9008ae020a901dc` |

For every row, removing only the exact 12-line public custody block restores
the extracted source bytes and SHA-256. The public hashes differ only because
the required custody block records repository, commit, extracted tree, source
path, destination path, date, and theorem-surface classification.

The normalized Lean bodies contain no `Skunkworks`,
`PromotionCandidates`, private review/archive import, `sorry`, `admit`,
custom `axiom` or `constant`, `unsafe`, `native_decide`, or
`Classical.choice`. The required custody block names the relative extracted
source path; that metadata is not a Lean import and is excluded by the
normalized-body check.

## Custody and target wiring

All ten sources are:

```text
Custody-Class: PUBLIC-SHIPPED
Surface-Role: PUBLIC-EVIDENCE
```

The separately rooted Mathlib-free public-evidence targets are:

```text
GovernedTransitionBoundaries
GovernedTransitionBoundariesEvidence
```

`scripts/public-custody.tsv` and `scripts/public-targets.tsv` contain the
corresponding exact rows. `scripts/stable-surfaces.tsv` is byte-identical to
the public baseline. The V15 stable census remains 115 files, twelve roots,
and 142 ownership relations. After this crossing the whole public tree has
283 Lean files: 115 stable, 167 public evidence, and one repository aggregate.

No pre-existing public Lean module imports the new family. The only imports of
`LeanProofs.GovernedTransitionBoundaries*` occur inside the ten-file family.

## Semantic preservation

No public namespace substitution was required: the extracted source already
used the destination namespaces
`LeanProofs.GovernedTransitionBoundaries` and
`LeanProofs.GovernedTransitionBoundariesEvidence`. The crossing relation is
therefore definitionally identical at the source level after removing the
custody block.

The private correspondence target recompiled at the pinned source tip and
preserved:

- definitionally equivalent generic relation applications;
- all four generic theorem signatures;
- the mapped 1,024-entry source enumeration;
- the 128-mask coordinate language;
- target and order-relative exactness, leastness, uniqueness, membership,
  count, and duplicate freedom;
- the deterministic-carrier restriction;
- the five-target and six-target result tables; and
- the five fixed native-fixture tables or inhabitation statuses.

The generic layer retains the distinction between explicit total-decoder
factorization and fibre determination. The finite leastness results remain
relative to `internalTarget`, the declared seven-coordinate language, and
`AtlasSelection.Includes`. The native fixtures remain fixed-policy,
two-context, budget-two, one-occurrence-link, and modeled-hidden-relation
results.

## Axiom footprints

The public qualification target replayed all 29 headline theorem footprints:

| Class | Exact footprint |
| --- | --- |
| generic four | none |
| source and selection lengths; selection duplicate freedom; exact-mask count and duplicate freedom | none |
| source coverage | `[propext, Quot.sound]` |
| selection coverage; five-target factorization; modeled hidden-relation and six-target exclusions; authorization witness | `[propext]` |
| exactness iff, leastness, uniqueness, exact-mask membership and classification | `[propext, Quot.sound]` |
| selected-context, realizability, occurrence-link, and admitted-interface witnesses | none |

No headline depends on `sorryAx` or `Classical.choice`.

## Public verification

Each command below exited zero:

```text
lake build GovernedTransitionBoundaries
lake build GovernedTransitionBoundariesEvidence
lake build
lake build LeanProofs AdmissibilityEvidenceMathlib ViewSemanticsEvidenceMathlib
lake build V15Integration V15IntegrationQualification
python3 scripts/check-v15-continuity-rename.py
python3 scripts/check-v15-integration.py
python3 scripts/check-v15-public-qualification.py
bash scripts/check-governed-transition-boundaries-crossing.sh
bash scripts/check-governed-transition-boundaries-footprint.sh
bash scripts/audit-axioms.sh
bash scripts/audit-native-decide.sh
bash scripts/check-mathlib-pin.sh
bash scripts/check-custody-classes.sh
bash scripts/check-mathlib-free-targets.sh
bash scripts/check-viewsemantics-isolation.sh
bash scripts/check-witnessed-footprint.sh
bash scripts/check-paid-recomposition-footprint.sh
bash scripts/check-judgment-orientation-footprint.sh
bash scripts/check-pathverdict-footprint.sh
bash scripts/check-calculus-footprint.sh
bash scripts/check-viewsemantics-footprint.sh
(cd downstream/wdc-v2-consumer && lake build)
git diff --check
```

The V15 integration checker excludes exactly the ten paths in the source
table from its historical whole-`LeanProofs` freeze. A negative-control run
omitting one exclusion failed closed. Every pre-existing V15 declaration,
digest, source pin, semantic check, and negative classification remains
checked. The V15 public qualification gate reported 2,606 declarations, 953
theorems, 735 hostile-module declarations, and twelve representative
collapses.

## Private qualification replay

Each command below exited zero from the private formalization project:

```text
lake build V16GovernedTransitionBoundariesExtracted
lake build V16GovernedTransitionBoundariesExtractionCorrespondence
python3 PromotionCandidates/V16GovernedTransitionBoundaries/Extracted/scripts/check_imports.py
python3 scripts/formalization_audit.py check
```

The private correspondence build completed 164 jobs, the import guard found
ten Lean files and fifteen direct edges with
`LeanProofs.ViewSemantics.Core` as the sole project-local dependency, and the
formalization audit passed 71 checks.

## Public changes

Added:

- the ten authorized Lean destinations;
- `docs/V16-GOVERNED-TRANSITION-BOUNDARIES-CANDIDATE.md`;
- this receipt;
- `scripts/check-governed-transition-boundaries-crossing.sh`; and
- `scripts/check-governed-transition-boundaries-footprint.sh`.

Modified:

- `.github/workflows/lean_action_ci.yml`;
- `lakefile.toml`;
- `scripts/check-v15-integration.py`;
- `scripts/check-v15-public-qualification.py`;
- `scripts/public-custody.tsv`; and
- `scripts/public-targets.tsv`.

Unchanged:

- `scripts/stable-surfaces.tsv`;
- every pre-existing Lean source;
- every V15 theorem, declaration manifest, source digest, and public receipt;
- release metadata; and
- all tags and releases.

## Explicit exclusions

No file was copied from:

- `Skunkworks/`;
- the original `PromotionCandidates/` qualification wrappers;
- `ExtractionCorrespondence.lean`;
- private semantic audits or qualification freezes;
- research dockets or prior-art search logs;
- unifier graveyard records;
- downloaded papers or retained third-party sources;
- private campaign or product-consequence assessments; or
- source-archive metadata not selected for public documentation.

## Public commits before this receipt

| Commit | Content |
| --- | --- |
| `3ced60c6dd14aa50aa182c3669b08679116d77f2` | governed-transition boundary core |
| `09bd81ed44b2f94d73541329954481583b94d465` | bounded evidence fixtures and qualification |
| `31c19e333e3d986f2245ee3bb706e9108ee0e7c2` | candidate thesis, scope, attribution, and bibliography |
| `160a97ffb17ae3c7cd1f69ffce61268ee17074ef` | public-evidence targets, custody, CI, exact crossing gate, footprint gate, and V15 coexistence exclusions |

## Unearned and unperformed

This crossing makes no novelty, priority, Hennessy–Milner, statistical
sufficiency, general authorization, general temporal-validity, general
amalgamation, causal-attribution, attestation-correctness, universal
six-way-independence, research-OS-correctness, product-readiness, stable-
compatibility, V16-finality, or release claim.

No tag, GitHub release, Zenodo action, version change, release-metadata edit,
or public announcement was performed.
