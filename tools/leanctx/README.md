# leanctx

Witness layer for the Lean corpus.

**Phase 1.5 (this version):** hard witnesses + working-tree scope
demotion. No semantic claim map, no doctrine mapping, no promotion
readiness, no public/scratch classification. The tool testifies to
facts it can actually witness; everything else is `gap_blocks` or
`out_of_scope_demotes`.

## Evidence algebra

Every command returns a JSON receipt typed by one of four evidence
modes:

| Mode | Meaning | Discharges downstream? |
|---|---|---|
| `witnessed` | Deterministic fact observed by the tool (source occurrence, module path, declaration candidate, build pass/fail at a specific SHA). | YES — for the claim it actually witnesses, and only if currency holds. |
| `asserted` | A value loaded from a registry or written by a human/agent. The tool witnesses that someone asserted it, not its truth. | NO. The downstream caller may quote the assertion as advisory only. (Not produced by any Phase 1 command.) |
| `gap_blocks` | A witness should exist for this kind of claim but the tool cannot produce one. | NO — and downstream action should stop until a witness exists. (No Silent Conversion: incomplete assessment must not clear downstream action.) |
| `out_of_scope_demotes` | The claim is not witnessable by this system in principle (e.g., semantic mapping from prose to a theorem). | NO — but downstream may proceed as advisory only. |

## Staleness

Staleness is NOT a peer evidence variant. A build receipt is
witnessed only relative to its `repo_sha`. At read time:

* If `receipt.repo_sha == HEAD` AND the working tree is clean,
  the receipt is `current` and discharges a "builds now" claim.
* Otherwise the receipt is `stale` — historical evidence only.

`leanctx receipt-valid` is the canonical way to check currency.
There is no harvestable `value` field on a stale receipt that an
agent can re-use to silently discharge a current claim.

## Custody scope (added in Phase 1.5)

Every `witnessed` receipt carries a `custody_scope` field:

| Scope | Meaning | Discharges SHA-bound claims? |
|---|---|---|
| `at_sha` | The witness is bound to a repo SHA — e.g., git-tracked file content, a clean build at HEAD. | YES (subject to currency check). |
| `working_tree_only` | The witness applies to the filesystem state — includes untracked files, dirty edits, etc. | **NO.** The receipt carries explicit `discharges` and `does_not_discharge` arrays so the downstream caller cannot quietly promote a worktree fact to a corpus fact. |

### Why this exists (the lake/git asymmetry)

`lake build` and `git grep` testify to **different courts**:

* `lake build` witnesses filesystem reality — it can see and compile
  an untracked `.lean` file just fine.
* `git grep` witnesses tracked-repo reality — by default it cannot
  see untracked files; they have no SHA-bound identity.
* `receipt-valid` witnesses current admissibility relative to HEAD
  + clean working tree.

These are not bugs in either tool; they are correct for what each
tool is actually witnessing. The asymmetry becomes visible when an
agent creates a new `.lean` file: `lake build` reports success,
`git grep` reports zero matches for the new declarations, and
`receipt-valid` refuses to discharge a current claim because the
tree is dirty. All three are correct simultaneously.

`leanctx` records which court each receipt comes from via
`custody_scope`, so the downstream caller (or governor) can refuse
to quietly conflate them.

### Default behavior is `tracked`

`grep` and `decl` default to `--scope=tracked` (git-tracked files
only, `custody_scope: at_sha`). Adding `--scope=worktree` includes
untracked files but emits the receipt with `custody_scope:
working_tree_only` and explicit `discharges` / `does_not_discharge`
arrays.

`module` always uses filesystem check (it tests whether the file
exists on disk), so it always emits `custody_scope:
working_tree_only` — even if the resolved file is git-tracked, the
verification was at the filesystem layer, not the SHA layer.

`build` emits `custody_scope: at_sha` when the working tree is
clean and `custody_scope: working_tree_only` when dirty — because a
build against a dirty tree witnessed lake's view of an off-SHA
filesystem state.

The default refusing untracked-file visibility is deliberate:
uncommitted scratch should not silently become corpus fact. The
worktree mode is available when an agent (e.g., during iterative
scratch creation) needs to verify its own just-written file
exists; the receipt cannot then be used to discharge a SHA-bound
corpus claim.

## Commands

### `leanctx head`

Return current HEAD SHA + dirty status.

```bash
$ leanctx head
```

Returns `witnessed` with `head_sha` and `dirty`.

### `leanctx grep <literal> [--scope=tracked|worktree]`

Literal source search (uses `git grep --fixed-strings`).

```bash
$ leanctx grep "separation invariant"                  # tracked (default)
$ leanctx grep "MyNewClass" --scope=worktree           # include untracked
```

Returns `witnessed` source occurrences with file/line/text + repo
SHA. **A grep hit is witnessed only as a string occurrence at a
location.** The caller must not promote it to "this concept is
defined here."

Default `--scope=tracked` searches only git-tracked files
(`custody_scope: at_sha`). `--scope=worktree` includes untracked
files and emits `custody_scope: working_tree_only` with explicit
non-discharge of SHA-bound claims.

### `leanctx module <Module.Name>`

Resolve a module name (dot-separated) to its source path. Returns
`witnessed` paths if the file exists, or `gap_blocks` if not. Does
NOT classify the module as scratch/public/promoted — that is
explicitly Phase 2 work and requires an assertion registry.

```bash
$ leanctx module LeanProofs.Scratch.BridgeInterfaces
```

### `leanctx decl <DeclName> [--scope=tracked|worktree]`

Find declaration candidates via conservative regex over Lean source
files. Scans for `<kind> <name>` patterns where `<kind>` is in a
closed list: `theorem def lemma abbrev inductive structure class
instance axiom example opaque`.

```bash
$ leanctx decl EvidenceInput                       # tracked (default)
$ leanctx decl ClaimKindBridge.decide
$ leanctx decl MyJustCreatedDef --scope=worktree   # include untracked
```

Returns `witnessed` candidates (with file/line/kind/source-line) if
matches found, or `gap_blocks` if none. **Returns multiple
candidates without semantic disambiguation** — two declarations with
the same name in different namespaces are both returned. The caller
chooses.

Will not invent declaration names. Will not match `<kind>
NAME.something` (use the namespaced full name explicitly).

Default `--scope=tracked` searches only git-tracked files
(`custody_scope: at_sha`). `--scope=worktree` includes untracked
files and emits `custody_scope: working_tree_only`. The worktree
mode is useful for verifying a just-written file's declarations
exist on disk; the receipt cannot then be used to discharge a
SHA-bound corpus claim.

### `leanctx build <Module.Name>`

Run `lake build <Module.Name>` and emit a build receipt with the
command, exit status, repo SHA, dirty flag, lake version, output
digests, and a tail of stdout/stderr.

```bash
$ leanctx build LeanProofs.Scratch.ProvenanceProfiles > my-receipt.json
```

The receipt is witnessed at the recorded SHA. To check whether it
discharges a current claim, use `receipt-valid`.

### `leanctx receipt-valid <receipt-file>`

Check whether a prior receipt is current. Reads the receipt's
`repo_sha`, compares to current HEAD, and accounts for working-tree
dirtiness.

```bash
$ leanctx receipt-valid my-receipt.json
```

* If `repo_sha == HEAD` AND working tree clean → `validity:
  "current"`, `discharges_current_claim: true`.
* Otherwise → `validity: "stale"`, `discharges_current_claim: false`,
  with a note that the receipt is historical only.
* If the receipt has no `repo_sha` → `out_of_scope_demotes` (the
  tool cannot witness its currency).

## Exit codes

* `0` — successful witnessed result OR a deliberate refusal that
  matches expectation (current receipt, head returned, etc.).
* `1` — `gap_blocks` (downstream should stop), `out_of_scope_demotes`,
  or stale receipt.

In governed pipelines, treat non-zero as "no current witness; do not
proceed."

## What this tool does NOT do (Phase 1 non-goals)

- No prose-to-Lean claim index.
- No semantic equivalence detection.
- No promotion readiness check.
- No "this theorem formalizes X" claims.
- No governor over arbitrary English.
- No public/scratch/promoted classification. (Phase 2 may add an
  assertion registry; even then the classification will be emitted
  as `asserted`, never `witnessed`.)
- No claim-kind discharge over a closed claim language. (Phase 3.)

If you find yourself wishing the tool would "just tell you whether
this is the right module" or "just confirm this theorem maps to
that doctrine," that is the disease. Use the witnessed primitives
(`module`, `decl`, `grep`, `build`) to gather evidence; let the
human/agent argue the mapping; do not let `leanctx` testify to
something it cannot witness.

## Quick test

```bash
cd ~/git/lean
python3 tools/leanctx/leanctx.py head
python3 tools/leanctx/leanctx.py module LeanProofs.Scratch.BridgeInterfaces
python3 tools/leanctx/leanctx.py decl EvidenceInput
python3 tools/leanctx/leanctx.py grep "separation invariant"
python3 tools/leanctx/leanctx.py build LeanProofs.Scratch.ProvenanceProfiles > /tmp/r.json
python3 tools/leanctx/leanctx.py receipt-valid /tmp/r.json
```
