# leanctx Phase 1 — status report

**Filed:** 2026-06-08. **Phase:** 1 (witness half only). **Imported by:** nobody (standalone Python tool under `tools/leanctx/`).

## What this tool can witness

Phase 1 emits `witnessed` evidence — receipts backed by deterministic
external oracles — for exactly the following kinds of facts:

| Witness | Oracle | Receipt fields |
|---|---|---|
| HEAD SHA + working-tree dirty status | `git rev-parse HEAD`, `git status --porcelain` | `head_sha`, `dirty` |
| Literal source string occurrences | `git grep --fixed-strings` at a repo SHA | `file`, `line`, `text`, `repo_sha` |
| Module-name → source-path resolution | filesystem check under conventional Lean layout | `module`, `paths`, `repo_sha` |
| Declaration candidate (source pattern) | `git grep` over `<kind> <name>` patterns, closed kind list | `file`, `line`, `kind`, `source_line` |
| `lake build` result for a module at a SHA | `lake build <module>` exit code + output digests | `module`, `status`, `command`, `exit_code`, `stdout_sha256`, `stderr_sha256`, `lake_version`, `repo_sha`, `dirty` |
| Receipt currency at HEAD | repo_sha comparison + dirty check | `validity`, `discharges_current_claim`, `current_head` |

Each witnessed result is bound to a specific `repo_sha`. Staleness is
computed at read time by `receipt-valid` — there is no harvestable
`value` field on a stale receipt that an agent could re-use to
discharge a current claim.

## What this tool refuses

Phase 1 emits `gap_blocks` (downstream action stops) for:

- Module name resolution when no source file exists for the dotted name.
- Module name with invalid identifier syntax.
- Declaration name with no source-pattern match across the closed
  kind list.
- Receipt file not found / unparseable JSON.
- Missing external tooling (git / lake).

Refusal is the load-bearing behavior — the tool returns
`gap_blocks` rather than fabricate plausible matches. The
declaration-search regex is conservative; it will miss declarations
that use unusual layout (e.g., custom syntax extensions) and return
`gap_blocks` rather than guess.

## What this tool demotes (advisory only)

Phase 1 emits `out_of_scope_demotes` for:

- Receipt-currency checks on receipts that carry no `repo_sha`. The
  tool cannot witness whether such a receipt is current; the caller
  may quote the receipt's content advisorily but not as a current
  witness.

Phase 1 does NOT yet have a path to emit `out_of_scope_demotes` for
semantic claims (e.g., "this theorem formalizes X"). That is
deliberate — Phase 1 does not accept English claims as input;
there is nothing to demote because nothing was asked.

## What remains out of scope (intentionally absent from Phase 1)

| Out-of-scope item | Reason it is absent |
|---|---|
| Prose → Lean semantic mapping index | Cannot be witnessed by any deterministic oracle; would silently upgrade signing to witnessing. |
| `public` / `scratch` / `promoted` classification | Requires an assertion registry; even then must be emitted as `asserted`, not `witnessed`. Reserved for Phase 2. |
| Theorem-formalizes-doctrine claims | Same disease. Out-of-scope by design. |
| Promotion-readiness checks | Composite judgment requiring registry input + build witness + asserted criteria. Reserved for Phase 3 governor. |
| Dependency-graph / public-surface extraction | Possible later via lean environment inspection (e.g., `lean --deps`); not built yet. |
| Closed-claim-language discharge governor | Reserved for Phase 3. The agent will submit structured claim objects; the governor mechanically checks them against the evidence algebra. |

## Verified smoke tests

Ran 2026-06-08 against `~/git/lean` at `9e88c52d`:

```text
leanctx head                                          → witnessed (head_sha + dirty:true)
leanctx module LeanProofs.Scratch.BridgeInterfaces    → witnessed (path found)
leanctx module LeanProofs.Nonexistent.Module          → gap_blocks (no source resolves)
leanctx module "not a module name"                    → gap_blocks (invalid format)
leanctx decl EvidenceInput                            → witnessed (1 candidate, Labelwatch.lean:165)
leanctx decl ClaimKindBridge                          → gap_blocks (no top-level `<kind> ClaimKindBridge` pattern)
leanctx decl ClaimKindBridge.decide                   → witnessed (1 candidate, BridgeInterfaces.lean)
leanctx decl ImaginaryDeclName                        → gap_blocks
leanctx grep "separation invariant"                   → witnessed (1 match, Labelwatch.lean:592)
leanctx build LeanProofs.Scratch.ProvenanceProfiles   → witnessed (status:pass, lake 5.0.0-src)
leanctx receipt-valid (current receipt, dirty tree)   → witnessed (validity:stale, dirty=true)
leanctx receipt-valid (fake old SHA)                  → witnessed (validity:stale)
leanctx receipt-valid (no repo_sha)                   → out_of_scope_demotes
```

All six commands behaved as designed. The `dirty` check correctly
prevented an otherwise-matching SHA from being treated as current
— which is the staleness rule doing its job.

## What the design pins down

The core discipline of Phase 1, restated for the next slice:

1. **Witnessed facts and asserted classifications must never share
   a JSON object as siblings at the same epistemic altitude.**
   Phase 1 enforces this by not having an assertion registry at all
   yet. When Phase 2 adds one, the assertion entries get their own
   evidence mode (`asserted`) and assertion envelope (with
   `asserted_by`, `asserted_at_sha`, `basis`), never co-mingled with
   witnessed receipts.

2. **No silent conversion from `gap_blocks` to `out_of_scope_demotes`
   (or vice versa).** The two refusals have opposite downstream
   semantics: `gap_blocks` *blocks*; `out_of_scope_demotes`
   *demotes*. Collapsing them is the disease the algebra exists to
   prevent.

3. **Staleness is a read-time predicate, not a packageable value.**
   A stale receipt does not carry a usable `value` field that an
   agent can re-emit. `receipt-valid` is the canonical staleness
   check; agents must run it before treating any prior receipt as
   evidence.

## Not yet built — recorded for the next packet

- **Phase 2: assertion registry.** A `corpus-status.yaml` (or
  similar) listing module classifications (`fenced_scratch`,
  `promoted_public`, etc.) loaded by the tool and emitted ONLY as
  `asserted`. The registry entries carry `asserted_by`,
  `asserted_at_sha`, `last_reviewed`, `basis`.

- **Phase 3: governor over a closed claim DSL.** Structured claim
  objects submitted by agents, validated by mechanical rules against
  the evidence algebra. Closed claim-kind language; no parsing of
  arbitrary English. Each claim kind has a known required-discharge
  rule.

- **Phase 2/3 are deliberately separate from Phase 1.** Building
  them before the witness half stabilizes is the path back into
  doctrine oatmeal.

## Curdling guard

This tool is fenced. It is not imported by any Lean code. It is not
a paper anchor. It produces JSON receipts to stdout and writes
nothing to the repo by itself. The artifact is the tool, not the
receipts; receipts are ephemeral by design (re-run to get a fresh
witness at current HEAD).
