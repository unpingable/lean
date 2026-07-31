# Lean Kernel Incident Qualification — leanprover/lean4 #14576 / #14577

Audit date: 2026-07-30. Auditor: Kimi Code CLI (automated bounded qualification audit).
Scope: public repository `https://github.com/unpingable/lean` only. No source was
modified; nothing was committed or pushed during the audit. All builds ran in
disposable clones.

**Audit scope.** Every replayed build surface in this report (toolchains A, B,
and C) was built at repository commit `ac40361` (tag `v16.0.0`). These
qualification documents were written after the audit and cherry-picked onto
`main` separately; no commit after `ac40361` is included in, or implied to be
covered by, the replayed build surface.

**STATUS: FINAL.** All three toolchain replays (stock v4.29.0, v4.29.0 +
isolated kernel fix, patched stable v4.32.2) completed.

Evidence manifest (sha256 of this report, the kernel patch, the probe, and
all build/gate logs, plus exact commands):
[`LEAN-KERNEL-INCIDENT-QUALIFICATION-2026-07-30-MANIFEST.json`](LEAN-KERNEL-INCIDENT-QUALIFICATION-2026-07-30-MANIFEST.json).

Evidence bundle (deliberately not in git):
`LEAN-KERNEL-INCIDENT-QUALIFICATION-2026-07-30-EVIDENCE.tar.zst`, SHA-256
`d72cf1af5d237f587b7a3b37bec585767bc2df1265b89a11125b2ea139c74303`.
Verification performed: archive listing, full decompression, and recursive
comparison with the source evidence all succeeded. The archive is a verified
strict superset of the manifest's 67 hashed artifacts; the two additional
files are `upstream-14577-full.patch` (the complete upstream #14577 patch)
and `sanity.lean` (the ordinary-elaboration sanity check).

---

## 1. Executive finding

**Not exposed within inspected surfaces.**

- The repository is pinned to `leanprover/lean4:v4.29.0`, which is **definitely
  affected** by the #14576 kernel bug (confirmed by direct reproduction, §2/§5D).
- No repository code, generated code, build tooling, or pinned dependency
  exercises the affected declaration path. The bug is reachable only through
  metaprogramming that submits a malformed inductive declaration via the checked
  `addDecl` API. Neither the repository nor any pinned dependency contains a
  single `.inductDecl` construction (§4).
- The complete corpus rebuilds cleanly under the patched stable v4.32.2 except
  for two `simp` normal-form drift sites and the Mathlib-island targets whose
  pinned dependencies predate v4.32.2 — all classified as ordinary version
  drift, none as reliance on rejected malformed behavior (§5).
- A controlled three-way replay (stock v4.29.0 / v4.29.0 + only the #14577
  kernel hunk / v4.32.2) demonstrates the separation of the patch from version
  drift within the replayed build surface: the
  isolated-fix toolchain rejects the upstream probe exactly like v4.32.2, yet
  rebuilds the **entire** corpus — including a full from-source build of all
  7,892 pinned mathlib modules — with **zero** kernel rejections and a
  byte-identical declaration census (§5B). Within that surface, every v4.32.2
  failure is attributable to unrelated 4.29→4.32 drift, not to the soundness
  patch.
- All footprint/axiom receipts that build at all under the patched kernel
  replay **identically** (§5C).

## 2. Upstream bug scope (Phase 0)

Verified against primary sources (not social media):

- Issue: [leanprover/lean4#14576](https://github.com/leanprover/lean4/issues/14576)
  — "Lean accepts a checked declaration containing a projection whose structure
  name does not match the value being projected … then proves `False` with no
  axioms." Reported against `4.34.0-nightly-2026-07-27`.
- Fix: [PR #14577](https://github.com/leanprover/lean4/pull/14577)
  "fix: missing check at kernel inductive declaration", merge commit
  `a39eab69e1eee9ad38f4efe507907b1026a77808`, merged 2026-07-28T13:39Z into
  `master`. Patch: `src/kernel/inductive.cpp` (+14/−3) plus two regression
  tests. Root cause: when eliminating a nested inductive occurrence `I Ds is`,
  the parametric arguments `Ds` were dropped from the generated auxiliary types
  and therefore escaped kernel type checking. The fix re-checks them once the
  inductive types being declared are available.
- Affected versions: every release/nightly whose kernel predates the fix. The
  bug is in long-standing kernel code (`environment::add_inductive`); no
  evidence any released version was immune. Confirmed affected empirically:
  v4.29.0 (this repository's pin).
- First patched versions: stable **v4.32.2** (published 2026-07-28T16:34Z;
  `compare v4.32.1...v4.32.2` shows exactly two commits, the #14577
  cherry-pick `8be817b3f631` and the release chore). Nightlies built after the
  2026-07-28T13:39Z merge (≥ 2026-07-29) are patched. **Not** patched:
  v4.32.1 and earlier, v4.33.0-rc1 (cut 2026-07-15).
- Kernel/elaborator path: `src/kernel/inductive.cpp`,
  `environment::add_inductive` → `elim_nested_inductive_fn`. Kernel-only; the
  elaborator is untouched by the fix.
- Exploit preconditions: a metaprogram must construct and submit an inductive
  declaration whose constructor types contain a nested occurrence with
  ill-typed parametric arguments (the public repro uses
  `liftCoreM <| addDecl <| .inductDecl …` with a `mkProj` of the wrong
  structure inside a nested type application).
- Ordinary source-level `inductive` declarations: **not implicated**. The
  malformed constructor type cannot be produced by the term elaborator; both
  upstream regression tests are `meta` programs using `addDecl` directly.
- Dependencies: a dependency can expose a downstream repository only if it
  ships a metaprogram that runs during downstream elaboration and calls
  `addDecl` with a malformed `.inductDecl`. Importing compiled oleans does not
  re-execute metaprograms. Dependency `addDecl` uses that construct
  `.defnDecl`/`.thmDecl`/`.mutualDefnDecl` do not pass through the affected
  kernel path at all.

## 3. Repository inventory (Phase 1)

- Clone provenance: `git clone https://github.com/unpingable/lean audit-pinned`
  at `pwd` `/home/jbeck/git/publean`; remote `origin` = the public URL;
  HEAD `ac403614fa49ba257955d359863d9cba0fc21b2f` (tag `v16.0.0`, branch
  `main`); working tree clean; `git log -1`: `ac40361 Tighten V16
  reader-facing claims`.
- Environment: `LEAN_PATH`, `LAKE_HOME`, `ELAN_HOME`, `ELAN_TOOLCHAIN` all
  unset/empty. No global module injection.
- `lean-toolchain`: `leanprover/lean4:v4.29.0`. Effective `lean --version`
  and `lake env lean --version`: `Lean (version 4.29.0, x86_64-unknown-linux-gnu,
  commit 98dc76e3c0a9b856c9b98726b713fb04fab16740, Release)`.
- Toolchain classification: **definitely affected** (predates fix; affectedness
  confirmed by reproduction, §5D).
- `lake-manifest.json`: 9 packages, all `git` type from public GitHub URLs —
  mathlib `6ef8cc27…`, plausible `d11647e9…`, LeanSearchClient `c5d5b8fe…`,
  importGraph `48d5698b…`, proofwidgets `00fe208b…`, aesop `7152850e…`,
  Qq `707efb56…`, batteries `be1a0299…`, Cli `7802da01…` (`inputRev v4.29.0`).
  **No `path` dependencies**; nothing resolves from sibling working trees; no
  imports from any private/skunkworks repository (all 283 `.lean` files are in
  the public tree; the manifest has no unexpected entries).
- `lakefile.toml`: 30 `lean_lib` targets; default targets are the Mathlib-free
  surfaces; Mathlib-reaching code is quarantined into `AdmissibilityEvidenceMathlib`,
  `ViewSemanticsEvidenceMathlib`, and the non-default `LeanProofs` aggregate.
  No plugins, no `precompileModules`.
- Corpus: 283 `.lean` files (281 under `LeanProofs/` + `formalization/`, root
  aggregate, downstream fixture); ~2,429 `theorem` declarations, ~750
  `inductive`/`structure` declarations, 31 `axiom`/`constant` declarations
  (classified by `scripts/axiom-policy.tsv`; audit PASS).
- Nested toolchain pins: `someone/lean-toolchain` = v4.29.0 (documentation
  directory, no Lean sources); `downstream/wdc-v2-consumer/lean-toolchain` =
  v4.29.0, manifest pins `lean_proofs` at tag `v2.0.0` (`b4bd02b7…`) — a
  historical pinned-evidence fixture.
- Fresh clones contained **no** `.lake/`, `build/`, `.olean`, generated-source,
  or qualification artifacts. Nothing could conceal a non-clean rebuild.
- Code generators: none that synthesize declarations. The only code generation
  is runtime instantiation of read-only declaration-census templates
  (`scripts/gt-c03-declaration-dump.lean.in`, temp-file copies of the
  `formalization/scripts/*DeclarationDump.lean` pattern).

## 4. Exposure search (Phase 2)

Search surface derived from the upstream fix: the affected path is entered only
by kernel submission of an inductive declaration (`.inductDecl`) — practically,
via `Lean.addDecl`/`liftCoreM addDecl`/declaration-API metaprogramming, since
ordinary `inductive` syntax produces elaborator-checked declarations.

Queries run over all 283 repo `.lean` files (plus scripts, templates,
`tools/`, and — after `lake` fetch — the full sources of all 9 pinned
dependencies):

- `addDecl|inductDecl|addDeclWithoutChecking|addAndCompile|Declaration\.` → **0 hits** in repo.
- `CommandElabM|TermElabM|MetaM|CoreM|runMetaM|liftCoreM|macro_rules|mkProj|mkApp*|mkForall|mkLambda` → **0 hits** in repo.
- `\bunsafe\b|implemented_by|\bextern\b|native_decide|\bopaque\b|\baxiom\b|\bmutual\b|macro|syntax|elab|sorry|admit` → only comments, `deriving` clauses, and intentional documented axioms (see below).
- `^mutual\s*$` → 0. No mutual inductive blocks exist.
- Nested-inductive heuristic (self-name applied inside another type former in
  constructor types, both `Former (... Self ...)` and `Former ... Self`
  patterns over `List/Array/Option/Except/Stream/Finset/Multiset/Subtype/Prod/Sum/Vector`)
  → 0 true hits; 4 candidate lines inspected and all false positives
  (`Sum.inl a) → CrossNaked` term context; `List Ticket`/`List Token`/`List Nat`
  fields of unrelated types).
- Dependency sources: `addDecl`/`inductDecl` grep across mathlib, batteries,
  aesop, Qq, plausible, LeanSearchClient, importGraph, proofwidgets, Cli.

Hits and classifications:

| Site | File:line | Class | Reasoning |
|---|---|---|---|
| Read-only census scripts | `formalization/scripts/ContinuityAdmissionDeclarationDump.lean:99` (+ 4 PJ tranche twins) | C | `run_cmd` blocks (elaboration-time execution) that only call `getEnv`, iterate `env.constants`, and `collectAxioms`. They never construct or add declarations. Cannot reach the affected path. |
| `deriving` clauses | many (e.g. `LeanProofs/TaxonomyGraph.lean:53`) | D | Only core classes (`DecidableEq`, `Repr`, `Inhabited`). Core deriving handlers produce ordinary definitions/instances through the elaborator. |
| Documented axioms | `LeanProofs/*` (31 decls) | D | Classified by `scripts/axiom-policy.tsv`; `audit-axioms.sh` PASS. Ordinary `axiom` commands. |
| mathlib `addDecl` uses | `Mathlib/Tactic/Sat/FromLRAT.lean:565,578,595`; `Mathlib/Tactic/HigherOrder.lean:94`; `Mathlib/Tactic/MkIffOfInductiveProp.lean:328`; `Mathlib/Tactic/Simps/Basic.lean:1002`; `Mathlib/Util/AddRelatedDecl.lean:74`; `Mathlib/Util/CompileInductive.lean:70,117,173`; `Mathlib/Tactic/Translate/*` | C | All construct `.defnDecl`/`.thmDecl`/`.mutualDefnDecl` — none pass through `add_inductive`. Also: the repository's 6 Mathlib-importing files invoke none of these tactics (they contain no meta constructs at all), so they never execute downstream regardless. |
| batteries `addDecl` uses | `Batteries/Tactic/Alias.lean:113,150`; `Batteries/Tactic/OpenPrivate.lean:164`; `Batteries/Util/Cache.lean` | C | Alias/def re-registration (`defnDecl`/`thmDecl`) and local-cache naming; not inductive declarations; not invoked by repo code. |
| aesop/Qq `addDecl` | `Aesop/Util/Basic.lean:446`; `Qq/Commands.lean:27`; `Qq/Macro.lean:210,353` | C | All are **local-context** `LocalContext.addDecl`, a different API unrelated to environment declaration submission. |
| `.inductDecl` anywhere | — | — | **Zero hits in the entire build graph** (repo + all 9 dependencies). The affected declaration kind is never constructed directly. |
| Uncategorized/uncertain | — | — | None requiring reproduction. |

Nested/mutual inductive determination: the corpus contains no `mutual` blocks
and no detected nested inductives. Independently, every inductive in the corpus
enters the kernel through the ordinary `inductive` command elaborator, which
produces type-correct constructor types; per §2 the upstream bug is not
reachable from that path. Classification D for the entire inductive corpus.

## 5. Clean-rebuild evidence (Phase 3 + controlled replay)

Three toolchains:

- **A. stock v4.29.0** (repository pin) — elan binary release, commit `98dc76e3`.
- **B. v4.29.0 + only the #14577 kernel fix** — local from-source build:
  `git clone --depth 1 --branch v4.29.0`, `git apply` of the
  `src/kernel/inductive.cpp` hunk of commit `a39eab69` (applies cleanly,
  +14/−3, no hand-porting, no test files), cmake release build (details and
  environment workarounds in §5B). Library, elaborator, tactics identical to
  A; elan-linked as `v4.29.0-kfix`.
- **C. patched stable v4.32.2** — elan binary release, commit `f3b06c70`.

Clones: `audit-pinned/` (A, pristine pin), `audit-patched/` (C; only
`lean-toolchain` files overridden), `audit-kfix/` (B; same tree, toolchain
overridden to the local build). Canonical tree untouched; `.lake/` is
gitignored; no commits anywhere.

### 5A. Stock v4.29.0 (baseline)

- `lake exe cache get` → success (mathlib olean cache).
- `lake build` (default, Mathlib-free) → **PASS** (236 jobs).
- `lake build LeanProofs V15Integration V15IntegrationQualification
  AdmissibilityEvidenceMathlib ViewSemanticsEvidenceMathlib` → **PASS**
  (8,527 jobs).
- Footprint/audit battery — **all PASS**:
  `check-witnessed-footprint.sh` (12 receipts), `check-paid-recomposition-footprint.sh`
  (52 theorem footprints), `check-judgment-orientation-footprint.sh` (13),
  `check-pathverdict-footprint.sh` (36), `check-calculus-footprint.sh` (191),
  `check-viewsemantics-footprint.sh`, `check-viewsemantics-isolation.sh`,
  `check-governed-transition-boundaries-crossing.sh` (10 byte-pinned files),
  `check-governed-transition-boundaries-footprint.sh` (29 theorem footprints),
  `audit-axioms.sh`, `audit-native-decide.sh`, `check-mathlib-pin.sh`,
  `check-mathlib-free-targets.sh`, `check-custody-classes.sh` (283 files,
  142 ownerships), `check-v15-continuity-rename.py` (1,005 declarations),
  `check-v15-integration.py` (4 PJ manifests, 1,950 cumulative declarations),
  `check-release-qualification.py` (18 claim invariants; census: **2,606
  declarations, 953 theorems**, 735 hostile-module declarations, 12
  representative collapses).
- Downstream fixture `(cd downstream/wdc-v2-consumer && lake build)` → **PASS**
  (19 jobs, against `lean_proofs` v2.0.0 pin).

### 5B. v4.29.0 + isolated kernel fix (controlled replay)

Toolchain build: the `src/kernel/inductive.cpp` hunk of `a39eab69` applies
**cleanly** to the v4.29.0 tag (`git apply --check` exit 0; no hand-porting,
no test files, no other changes — the elaborator, tactics, library, and
dependency pins are bit-identical to A). The patch file is preserved as
`kernel-14577-v4.29.0.patch` in the evidence bundle. Built from source with
cmake 3.28.3 / gcc 13.3.0. Two host-specific build accommodations were needed
on the audit machine (neither is part of the recipe's logic; both state
prerequisites any builder can satisfy their own way): the machine's `cmake`
entry point was a broken shim, so a working cmake binary was invoked
explicitly; and GMP development files — a standard Lean build prerequisite —
were absent system-wide, so they were supplied through cmake's
include/library search paths, linking against the shared GMP runtime.
Result: full stage0+stage1 build succeeded;
`lean --version` reports `4.29.0, commit 98dc76e3…` as expected. Linked into
elan as `v4.29.0-kfix`.

Fix activation check (before any repository build): the §5D probe is
**rejected** by this build with `error: (kernel) invalid projection  w.1` —
identical to C — while an ordinary inductive + theorem sanity file elaborates
with `'ok' does not depend on any axioms`. The repaired kernel is active;
everything else behaves as v4.29.0.

Replay results (fresh clone `audit-kfix`, same HEAD `ac40361`):

- `lake exe cache get` → rc=1: mathlib's cache tool refuses because the
  toolchain *name* (`v4.29.0-kfix`) does not textually match mathlib's
  `lean-toolchain`. **Benign and, in fact, strengthening:** the fallback was a
  complete from-source build of every pinned dependency — all 7,892 mathlib
  modules (7,892 `.olean` + 7,892 `.c` artifacts) plus Batteries, aesop, Qq,
  etc. were elaborated and kernel-checked by the *fixed* 4.29 kernel with
  **zero rejections**. (On A, mathlib came from the official pre-built cache
  instead.)
- `lake build` (default) → **PASS, 236/236 jobs** — identical to A.
- Non-default targets (`LeanProofs V15Integration V15IntegrationQualification
  AdmissibilityEvidenceMathlib ViewSemanticsEvidenceMathlib`) → **PASS**
  (8,533 jobs; job-count delta vs A is replay-accounting only, both fully
  successful). Both C-drift sites — `BreakGlass/Native.lean` and
  `Continuity…/Hostile.lean` — **compile green on B**, demonstrating within
  the replayed build surface that their C failures are 4.29→4.32 simp drift,
  not kernel-fix effects.
- All 13 shell gates **PASS** (same battery as §5A), all 3 python gates
  **PASS**: `check-release-qualification.py` reproduces the census exactly —
  **2,606 declarations, 953 theorems**, 735 hostile-module declarations, 12
  representative collapses — byte-identical to A.
- Downstream fixture (toolchain overridden to `v4.29.0-kfix`) → **PASS**
  (19 jobs).
- Rejections caused by the repaired kernel across the entire corpus and all
  dependencies: **zero**. Ordinary source/tactic drift on B: **zero**
  (B shares A's elaborator). Dependency incompatibility on B: **zero**
  (B shares A's library/ABI). Indeterminate failures on B: **zero** (the only
  nonzero exit was the cache tool's toolchain-name check, explained above).

A/B/C separation of effects: every failure observed on C is absent on B.
Within the replayed build surface, this demonstrates that none of the C
failures is caused by the kernel soundness patch; all are attributable to
unrelated language/simp/dependency drift between v4.29.0
and v4.32.2. The kernel fix itself changes no behavior anywhere in this
repository's build graph — consistent with §4's finding that nothing
constructs inductive declarations outside the ordinary elaborator.

### 5C. Patched stable v4.32.2

- `lake build` (default, Mathlib-free) → **235/236 modules green**; one failure:
  - `LeanProofs/Admissibility/Calculus/Instances/BreakGlass/Native.lean:814,828`
    — `simpa … using commit.receiptValid` / `commit.entryPayload` no longer
    closes: "Type mismatch: After simplification …". **Classification: ordinary
    version drift** (simp normal-form change between 4.29 and 4.32). The
    "declaration uses `sorry`" warning in the same build is a *consequence* of
    these two failed proofs (Lean inserts synthetic sorries for failed proof
    terms); the source contains no literal `sorry`.
- Non-default targets:
  - `Continuity.Admission.Qualification.Hostile.lean:59` — same simp-drift
    signature. **Ordinary version drift.**
  - Mathlib-island targets (`AdmissibilityEvidenceMathlib`,
    `ViewSemanticsEvidenceMathlib`, root `LeanProofs`) — **blocked by dependency
    incompatibility**, not repo code: pinned Batteries/Qq/Aesop/Plausible/mathlib
    (built for v4.29.0) fail under v4.32.2, e.g.
    `Batteries/Classes/Cast.lean:12` "may not access declaration … marked as
    `meta`" (4.32 meta-visibility rule change), `Qq/Delab.lean:74` type
    mismatch. All **dependency version drift**.
  - No `(kernel)` errors of any kind anywhere in the build — in particular no
    "invalid projection" or nested-inductive rejections. Nothing in the corpus
    depends on the previously-accepted malformed behavior.
- Footprint battery: 7/9 Lean-building gates PASS with **byte-identical
  receipts** to baseline, including all 29 governed-transition-boundaries
  theorem footprints and all axiom prints (e.g. ProofTheory `cut` ≡
  `[propext, Quot.sound]` on both kernels). The 2 failures trace to the drift
  above, not the kernel: `check-calculus-footprint.sh` includes the drifted
  `BreakGlass.Native`; `check-viewsemantics-footprint.sh` additionally builds
  `ViewSemanticsEvidenceMathlib` (dependency-blocked; the Mathlib-free
  `ViewSemantics ViewSemanticsEvidence` targets alone build green, 31 jobs).
  `check-v15-continuity-rename.py` / `check-v15-integration.py` /
  `check-release-qualification.py` fail on the same `Hostile.lean` drift
  (the rename gate compiles the pre-rename twin of the same file).
- Downstream fixture under C (toolchain overridden) → **PASS** (19 jobs); the
  v2.0.0-era Mathlib-free Witnessed subset is drift-clean across 4.29→4.32.2.

### 5D. Toolchain probe (bounded mechanism check)

Upstream's minimal regression file (`tests/elab/issue_14576_min.lean`, the
declaration-level probe only — not the `False` exploit) was run on all three
toolchains:

- A (stock v4.29.0): logs `E accepted` — kernel **accepts** the malformed
  nested inductive. (Harness note: the `#guard_msgs` wrapper was stripped for
  the run, producing an unrelated trailing parse error; the meta program
  itself executed and printed its log messages.)
- B (v4.29.0 + isolated fix): `error: (kernel) invalid projection  w.1` —
  kernel **rejects** it.
- C (v4.32.2): `error: (kernel) invalid projection  w.1` — kernel **rejects**
  it, identically to B.

This confirms A is affected, that the isolated hunk on v4.29.0 fully
reproduces C's rejection behavior for this bug class, and demonstrates
precisely which rejection the repaired kernel produces. No such rejection
occurred anywhere in the repository builds on any toolchain.

### Census comparison

| Metric | A (v4.29.0) | B (v4.29.0 + fix) | C (v4.32.2) |
|---|---|---|---|
| Default-target modules | 236/236 | 236/236 | 235/236 (1 simp-drift) |
| All targets incl. Mathlib islands | PASS | PASS (deps built from source, 7,892 mathlib modules, 0 rejections) | repo modules PASS; islands blocked by dependency drift |
| Release-qualification census | 2,606 decls / 953 theorems | 2,606 decls / 953 theorems (identical) | blocked at Hostile drift site (gate runs the dump over the same modules) |
| GTB theorem footprints | 29/29 replay | 29/29 replay (identical) | 29/29 replay, identical |
| Axiom receipts (all passing gates) | as attested | identical to A | identical to A |
| Kernel rejections of repo declarations | 0 | 0 | 0 |
| Probe (`issue_14576_min`) | accepted | **rejected** `(kernel) invalid projection` | **rejected** `(kernel) invalid projection` |

`#print axioms` parity is regression evidence only; it does not independently
detect kernel unsoundness (an exploit reports "no axioms" by design).

## 6. Residual risk and limits

- This audit does **not** establish universal soundness of the repository's
  proofs. A clean rebuild shows the corpus does not *rely on* the #14576
  malformed-declaration behavior; it says nothing about other kernel bugs,
  known or unknown.
- Textual search cannot prove a negative absolutely. Mitigations applied:
  searched dependency sources as well as the repo; searched API families
  (`addDecl`, `Declaration.`, elaboration monads, Expr constructors), not just
  the literal exploit identifiers; inspected the only elaboration-time code
  (`run_cmd` census scripts) by reading it; verified zero `.inductDecl`
  constructions in the whole build graph.
- Mathlib-island targets were not re-verified under the patched *stable* kernel
  on C (pinned dependencies do not compile under v4.32.2). This blind spot is
  materially narrowed by toolchain B: on v4.29.0 + the isolated fix, every
  pinned dependency — all 7,892 mathlib modules — was compiled from source and
  kernel-checked with zero rejections, and both Mathlib-island targets plus
  the root aggregate built green. The islands' own 6 Mathlib-importing files
  contain no metaprogramming and invoke no declaration-adding tactics.
- The `run_cmd` census scripts execute at elaboration time and could in
  principle be edited to do anything; they are evidence tooling, currently
  read-only, and covered by the tree-freeze gates.
- The toolchain probe stripped `#guard_msgs` (see §5D); the accept/reject
  signal is nonetheless unambiguous.
- Early `*_EXIT` shell captures in this audit's logs were pipeline artifacts;
  all conclusions rest on lake's own target-failure reporting and targeted
  rebuilds, not on those echoes.

## 7. Recommended disposition

1. **Record the qualification event** (this document). No quarantine of files
   or targets is warranted; nothing in the repository exercises the affected
   path.
2. **Update the pinned toolchain to ≥ v4.32.2 at the operator's convenience**
   — not as an emergency. Required work: repin mathlib + dependencies to a
   v4.32-compatible set (`lake update` + `scripts/check-mathlib-pin.sh`), and
   repair the two ordinary simp-drift sites
   (`BreakGlass/Native.lean:814,828`, `Continuity/Admission/Qualification/Hostile.lean:59`).
   Per repository governance this is an operator decision; this audit changes
   nothing.
3. No campaign replays are required beyond this audit: all receipts that build
   under the patched kernel replay identically.
4. No deeper dependency audit is indicated by these findings; the
   dependency-source scan found no `.inductDecl` construction anywhere.

## 8. Proposed qualification statement (research log)

> On 2026-07-30 the repository (HEAD `ac40361`, v16.0.0, toolchain
> `leanprover/lean4:v4.29.0`) was audited against Lean kernel issue
> leanprover/lean4#14576 (missing check at kernel inductive declaration; fixed
> by #14577, first patched stable v4.32.2). The pinned toolchain is affected
> (confirmed by reproduction of the upstream minimal probe), but the
> repository is not exposed: the bug is reachable only via metaprogramming
> that submits malformed inductive declarations through `addDecl
> <| .inductDecl`, and no such construction exists anywhere in the repository
> or its nine pinned dependencies (zero `.inductDecl` uses; all inductives
> arrive via the ordinary elaborator; no mutual or nested inductives present).
> A clean rebuild under patched stable v4.32.2 reproduces every axiom receipt
> and theorem footprint that builds at all; the only failures are two `simp`
> normal-form drift sites and Mathlib-island dependency drift, none of which
> is a kernel rejection. A controlled replay on a from-source v4.29.0 build
> carrying only the #14577 kernel hunk (confirmed to reject the upstream
> probe exactly as v4.32.2 does) rebuilds the entire corpus — including a
> from-source build of all 7,892 pinned mathlib modules — with zero kernel
> rejections and a byte-identical declaration census (2,606 declarations, 953
> theorems), demonstrating within the replayed build surface the separation of
> the soundness patch from unrelated version drift. The
> repository neither triggers nor relies on the rejected malformed behavior. Disposition: record the event; update the
> toolchain pin on the normal schedule. Successful compilation is evidence of
> non-reliance on this bug, not proof of universal soundness.
