#!/usr/bin/env python3
"""leanctx — witness layer for the Lean corpus.

Phase 1.5: hard witnesses + working-tree scope demotion. No semantic
claim map, no doctrine mapping, no promotion readiness. The tool
testifies to facts it can actually witness; everything else is
gap_blocks or out_of_scope_demotes.

The evidence algebra has four states:

    witnessed              — deterministic fact observed by the tool
    asserted               — value loaded from a registry; demoted, NOT
                              promoted to truth. (Not produced by any
                              command in Phase 1.5; reserved for Phase 2.)
    gap_blocks             — a witness should exist for this claim
                              but the tool cannot produce it.
                              Downstream action should stop.
    out_of_scope_demotes   — claim is not witnessable by this system.
                              Proceed only as advisory.

Custody scope (added in Phase 1.5):
    Every `witnessed` receipt carries a `custody_scope` field naming
    the layer the witness applies to:

        at_sha               — the witness is bound to a repo SHA
                              (e.g., git-tracked file content, the
                              committed result of a clean build).
                              Discharges SHA-bound corpus claims.

        working_tree_only    — the witness applies to the filesystem
                              state, not to any SHA. Includes
                              untracked files, dirty edits, etc.
                              Does NOT discharge SHA-bound claims;
                              the receipt carries explicit
                              `discharges` / `does_not_discharge`
                              fields so the downstream caller cannot
                              quietly promote a worktree fact into a
                              corpus fact.

    The two are separate courts. `lake build` witnesses filesystem
    reality (it can see untracked files); `git grep` witnesses
    tracked-repo reality (it cannot). `leanctx` records which court
    each receipt comes from so the downstream caller cannot conflate
    them.

Staleness rule (load-bearing):
    A build receipt is witnessed only relative to its repo_sha. At
    read time, if receipt.repo_sha != HEAD, it does NOT discharge a
    current "builds now" claim. Stale receipts are historical
    evidence only. There is no `stale` peer variant — staleness is
    a read-time predicate over `witnessed`, never a packageable
    value an agent can reuse.
"""

import argparse
import hashlib
import json
import re
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List, Optional

TOOL_VERSION = "0.1.5"


# ============== Repo helpers ==============


def _run(cmd: List[str], **kwargs) -> subprocess.CompletedProcess:
    """Run a subprocess with text capture."""
    return subprocess.run(cmd, capture_output=True, text=True, check=False, **kwargs)


def repo_root() -> Path:
    """Locate the repo root via git rev-parse."""
    result = _run(["git", "rev-parse", "--show-toplevel"])
    if result.returncode != 0:
        raise RuntimeError(f"Not in a git repo: {result.stderr.strip()}")
    return Path(result.stdout.strip())


def git_head_sha() -> str:
    result = _run(["git", "rev-parse", "HEAD"])
    if result.returncode != 0:
        raise RuntimeError(f"git rev-parse HEAD failed: {result.stderr.strip()}")
    return result.stdout.strip()


def git_is_dirty() -> bool:
    result = _run(["git", "status", "--porcelain"])
    if result.returncode != 0:
        return True  # conservative: assume dirty if we can't tell
    return bool(result.stdout.strip())


# ============== Evidence constructors ==============


def _envelope(extra: Optional[Dict[str, Any]] = None) -> Dict[str, Any]:
    env: Dict[str, Any] = {
        "tool": "leanctx",
        "tool_version": TOOL_VERSION,
        "generated_at": datetime.now(timezone.utc).isoformat(),
    }
    if extra:
        env.update(extra)
    return env


def witnessed(value: Any,
              receipt_extra: Optional[Dict[str, Any]] = None,
              custody_scope: str = "at_sha",
              discharges: Optional[List[str]] = None,
              does_not_discharge: Optional[List[str]] = None) -> Dict[str, Any]:
    """Construct a witnessed-evidence object.

    A witnessed result is the strongest evidence: a deterministic fact
    the tool observed (source occurrence, module path, declaration
    candidate, build pass/fail at SHA, etc.).

    `custody_scope` records which court the witness comes from:
      - 'at_sha': bound to a repo SHA; discharges SHA-bound claims.
      - 'working_tree_only': filesystem-level only; does NOT discharge
        SHA-bound claims. Receipts of this kind must carry explicit
        `discharges` / `does_not_discharge` so downstream callers do
        not silently promote worktree facts to corpus facts."""
    obj: Dict[str, Any] = {
        "mode": "witnessed",
        "custody_scope": custody_scope,
        "value": value,
        "receipt": _envelope(receipt_extra),
    }
    if discharges is not None:
        obj["discharges"] = discharges
    if does_not_discharge is not None:
        obj["does_not_discharge"] = does_not_discharge
    return obj


def asserted(value: Any, asserted_by: str, basis: List[str],
             extra: Optional[Dict[str, Any]] = None) -> Dict[str, Any]:
    """Construct an asserted-evidence object.

    Asserted means: a value loaded from a registry or written by a
    human/agent. The tool cannot witness its truth — it can only
    witness that someone asserted it. NOT produced by any Phase 1
    command; reserved for Phase 2's assertion registry."""
    return {
        "mode": "asserted",
        "value": value,
        "assertion": {
            "asserted_by": asserted_by,
            "asserted_at_sha": git_head_sha(),
            "basis": basis,
            **(extra or {}),
        },
    }


def gap_blocks(query: str, reason: str,
               required_witness: List[str]) -> Dict[str, Any]:
    """Construct a gap_blocks-evidence object.

    Gap-blocks means: a witness should exist for this kind of claim,
    but the tool cannot produce one. Downstream action should stop
    until the witness exists. (NNC: incomplete assessment must not
    clear downstream action.)"""
    return {
        "mode": "gap_blocks",
        "query": query,
        "reason": reason,
        "required_witness": required_witness,
        "receipt": _envelope(),
    }


def out_of_scope_demotes(claim: str, reason: str) -> Dict[str, Any]:
    """Construct an out_of_scope_demotes-evidence object.

    Out-of-scope means: the claim is not witnessable by this system
    in principle (e.g., a semantic mapping from prose to a theorem).
    The downstream caller may proceed but only as advisory; the
    claim cannot be promoted to witnessed truth."""
    return {
        "mode": "out_of_scope_demotes",
        "claim": claim,
        "reason": reason,
        "discharge": "advisory_only",
        "receipt": _envelope(),
    }


def emit(obj: Dict[str, Any]) -> None:
    """Emit a JSON receipt to stdout, pretty-printed for inspection."""
    json.dump(obj, sys.stdout, indent=2, sort_keys=True)
    sys.stdout.write("\n")


# ============== Commands ==============


def cmd_head(args: argparse.Namespace) -> int:
    """leanctx head — return HEAD SHA + dirty status."""
    try:
        sha = git_head_sha()
        dirty = git_is_dirty()
        emit(witnessed({
            "head_sha": sha,
            "dirty": dirty,
        }))
        return 0
    except RuntimeError as e:
        emit(gap_blocks("head", str(e), ["git_rev_parse_head"]))
        return 1


def cmd_grep(args: argparse.Namespace) -> int:
    """leanctx grep <literal> — literal source search.

    Default scope is 'tracked': searches only git-tracked files.
    With --scope=worktree, also includes untracked files (the
    receipt is then explicitly demoted to working_tree_only and
    will NOT discharge SHA-bound claims)."""
    literal = args.literal
    scope = args.scope
    try:
        root = repo_root()
        sha = git_head_sha()
    except RuntimeError as e:
        emit(gap_blocks("grep", str(e), ["git_repo_root"]))
        return 1

    cmd = ["git", "grep", "-n", "--fixed-strings", "--no-color"]
    if scope == "worktree":
        cmd.append("--untracked")
    cmd.extend(["--", literal])

    result = _run(cmd, cwd=root)

    matches: List[Dict[str, Any]] = []
    # git grep exits 0 with matches, 1 with no matches, >1 on error
    if result.returncode == 0:
        for line in result.stdout.splitlines():
            parts = line.split(":", 2)
            if len(parts) == 3:
                try:
                    matches.append({
                        "file": parts[0],
                        "line": int(parts[1]),
                        "text": parts[2],
                    })
                except ValueError:
                    continue
    elif result.returncode > 1:
        emit(gap_blocks(literal, f"git grep failed: {result.stderr.strip()}",
                        ["git_grep_executable"]))
        return 1

    value = {
        "query": literal,
        "scope": scope,
        "match_count": len(matches),
        "matches": matches,
    }
    receipt_extra = {
        "repo_sha": sha,
        "command": " ".join(cmd),
    }
    if scope == "worktree":
        emit(witnessed(
            value, receipt_extra,
            custody_scope="working_tree_only",
            discharges=["string_occurrence_in_worktree"],
            does_not_discharge=[
                "string_occurrence_at_sha",
                "corpus_claim_at_head",
            ],
        ))
    else:
        emit(witnessed(value, receipt_extra))
    return 0


_MODULE_NAME_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*(\.[A-Za-z_][A-Za-z0-9_]*)*$")


def cmd_module(args: argparse.Namespace) -> int:
    """leanctx module <Module.Name> — resolve module to source path.

    Tries the conventional Lean source layout (dot → slash). Returns
    witnessed paths if found; gap_blocks if not. Does NOT classify the
    module as scratch/public/promoted — that is Phase 2 registry work."""
    module = args.module
    if not _MODULE_NAME_RE.match(module):
        emit(gap_blocks(module, "module name has invalid format",
                        ["valid_module_name"]))
        return 1

    try:
        root = repo_root()
        sha = git_head_sha()
    except RuntimeError as e:
        emit(gap_blocks(module, str(e), ["git_repo_root"]))
        return 1

    parts = module.split(".")
    candidates = [
        root / Path(*parts).with_suffix(".lean"),
    ]

    found = []
    for cand in candidates:
        try:
            rel = cand.relative_to(root)
        except ValueError:
            continue
        if cand.exists() and cand.is_file():
            found.append(str(rel))

    if found:
        # File-existence is a filesystem-level check — works on
        # untracked files too. Honestly label it as worktree-scope.
        emit(witnessed(
            {"module": module, "paths": found},
            {"repo_sha": sha},
            custody_scope="working_tree_only",
            discharges=["file_exists_on_disk"],
            does_not_discharge=[
                "file_tracked_at_sha",
                "module_in_corpus_at_head",
            ],
        ))
        return 0
    else:
        emit(gap_blocks(
            module,
            f"no Lean source file resolves for module name {module}",
            ["lean_module_source_path"],
        ))
        return 1


_DECL_KINDS = ["theorem", "def", "lemma", "abbrev", "inductive",
               "structure", "class", "instance", "axiom", "example",
               "opaque"]


def cmd_decl(args: argparse.Namespace) -> int:
    """leanctx decl <DeclName> — find declaration candidates via conservative regex.

    Conservative: scans Lean source files for `<kind> <name>` patterns
    where <kind> is in the closed list above. May miss declarations
    that use unusual layout. Will NOT invent names; if no pattern
    matches, returns gap_blocks.

    Default scope is 'tracked' (git-tracked files only). With
    --scope=worktree, also searches untracked files (the receipt is
    then explicitly demoted to working_tree_only)."""
    name = args.decl
    scope = args.scope
    try:
        root = repo_root()
        sha = git_head_sha()
    except RuntimeError as e:
        emit(gap_blocks(name, str(e), ["git_repo_root"]))
        return 1

    candidates: List[Dict[str, Any]] = []
    name_escaped = re.escape(name)

    for kind in _DECL_KINDS:
        # Match at line start (with optional whitespace):
        #   <kind> <name>(:|<space>|<paren>|<brace>|<eol>)
        pattern = f"^\\s*{kind}\\s+{name_escaped}(\\s|:|\\(|\\{{|\\[|$)"
        cmd = ["git", "grep", "-n", "-E", "--no-color"]
        if scope == "worktree":
            cmd.append("--untracked")
        cmd.extend([pattern, "--", "*.lean"])
        result = _run(cmd, cwd=root)
        if result.returncode == 0:
            for line in result.stdout.splitlines():
                parts = line.split(":", 2)
                if len(parts) == 3:
                    try:
                        candidates.append({
                            "file": parts[0],
                            "line": int(parts[1]),
                            "kind": kind,
                            "source_line": parts[2].rstrip("\n"),
                        })
                    except ValueError:
                        continue
        elif result.returncode > 1:
            emit(gap_blocks(name, f"git grep failed: {result.stderr.strip()}",
                            ["git_grep_executable"]))
            return 1

    if candidates:
        value = {
            "decl": name,
            "scope": scope,
            "candidate_count": len(candidates),
            "candidates": candidates,
            "note": ("candidates are source-pattern matches; multiple "
                     "matches may be unrelated declarations in different "
                     "namespaces"),
        }
        receipt_extra = {
            "repo_sha": sha,
            "scanned_kinds": _DECL_KINDS,
        }
        if scope == "worktree":
            emit(witnessed(
                value, receipt_extra,
                custody_scope="working_tree_only",
                discharges=["decl_candidate_in_worktree"],
                does_not_discharge=[
                    "decl_exists_at_sha",
                    "corpus_claim_at_head",
                ],
            ))
        else:
            emit(witnessed(value, receipt_extra))
        return 0
    else:
        emit(gap_blocks(
            name,
            f"no conservative declaration pattern matches for {name}"
            f" (scope: {scope})",
            ["lean_decl_source_match"],
        ))
        return 1


def cmd_build(args: argparse.Namespace) -> int:
    """leanctx build <Module.Name> — run lake build and emit receipt.

    The build receipt records the command, exit status, repo SHA,
    dirty status, lake version, output digests, and a tail of stdout/
    stderr. The result is witnessed only at THIS repo_sha — staleness
    must be checked at read time via receipt-valid."""
    module = args.module
    try:
        root = repo_root()
        sha = git_head_sha()
        dirty = git_is_dirty()
    except RuntimeError as e:
        emit(gap_blocks(module, str(e), ["git_repo_root"]))
        return 1

    # Probe lake
    lake_version: Optional[str] = None
    try:
        v = _run(["lake", "--version"])
        if v.returncode == 0:
            lake_version = v.stdout.strip()
    except FileNotFoundError:
        emit(gap_blocks(module, "lake not found in PATH",
                        ["lake_executable"]))
        return 1

    cmd = ["lake", "build", module]
    started_at = datetime.now(timezone.utc).isoformat()
    result = _run(cmd, cwd=root)
    finished_at = datetime.now(timezone.utc).isoformat()

    stdout_digest = hashlib.sha256(result.stdout.encode()).hexdigest()
    stderr_digest = hashlib.sha256(result.stderr.encode()).hexdigest()

    receipt_value = {
        "module": module,
        "exit_code": result.returncode,
        "status": "pass" if result.returncode == 0 else "fail",
        "command": " ".join(cmd),
        "started_at": started_at,
        "finished_at": finished_at,
        "stdout_sha256": stdout_digest,
        "stderr_sha256": stderr_digest,
        "stdout_tail": "\n".join(result.stdout.splitlines()[-10:]),
        "stderr_tail": "\n".join(result.stderr.splitlines()[-10:]),
    }

    extra_envelope = {
        "repo_sha": sha,
        "dirty": dirty,
        "lake_version": lake_version,
        "validity_note": ("This receipt witnesses the build state at "
                          "repo_sha. It does NOT witness 'builds now' "
                          "if HEAD has moved or the tree is dirty. Use "
                          "`leanctx receipt-valid` to check currency."),
    }
    # If the working tree is dirty, lake saw files that aren't bound
    # to the SHA; demote the receipt to working_tree_only so it
    # cannot silently discharge a SHA-bound build claim.
    if dirty:
        emit(witnessed(
            receipt_value, extra_envelope,
            custody_scope="working_tree_only",
            discharges=["build_passes_in_worktree"]
                if result.returncode == 0 else ["build_failed_in_worktree"],
            does_not_discharge=[
                "build_passes_at_sha",
                "current_clean_build_claim",
            ],
        ))
    else:
        emit(witnessed(receipt_value, extra_envelope))
    return 0 if result.returncode == 0 else 1


def cmd_receipt_valid(args: argparse.Namespace) -> int:
    """leanctx receipt-valid <receipt-file> — check receipt currency vs HEAD.

    Reads a prior receipt's repo_sha and compares to current HEAD.
    A current receipt (sha == HEAD) discharges its claim; a stale
    receipt does NOT — it is historical evidence only. If HEAD is
    dirty, even a sha-matching receipt is treated as stale (the
    working tree differs from any committed state)."""
    receipt_path = Path(args.receipt_file)
    if not receipt_path.exists():
        emit(gap_blocks(str(receipt_path),
                        "receipt file does not exist",
                        ["receipt_file_exists"]))
        return 1

    try:
        with open(receipt_path) as f:
            receipt = json.load(f)
    except (json.JSONDecodeError, IOError) as e:
        emit(gap_blocks(str(receipt_path),
                        f"could not parse receipt as JSON: {e}",
                        ["receipt_parseable_json"]))
        return 1

    try:
        current_head = git_head_sha()
        dirty = git_is_dirty()
    except RuntimeError as e:
        emit(gap_blocks(str(receipt_path), str(e), ["git_repo_root"]))
        return 1

    # Look for repo_sha; standard envelope places it under receipt.repo_sha
    receipt_sha: Optional[str] = None
    if isinstance(receipt.get("receipt"), dict):
        receipt_sha = receipt["receipt"].get("repo_sha")
    if not receipt_sha:
        receipt_sha = receipt.get("repo_sha")

    if not receipt_sha:
        emit(out_of_scope_demotes(
            f"validity of receipt {receipt_path}",
            ("receipt does not carry a repo_sha; the tool cannot "
             "witness whether the receipt is current."),
        ))
        return 1

    sha_matches = (receipt_sha == current_head)
    is_current = sha_matches and not dirty

    value = {
        "receipt_file": str(receipt_path),
        "receipt_sha": receipt_sha,
        "current_head": current_head,
        "working_tree_dirty": dirty,
        "validity": "current" if is_current else "stale",
        "discharges_current_claim": is_current,
    }
    if not is_current:
        value["note"] = ("Receipt is historical evidence only. It does "
                         "NOT discharge a current claim; re-run the "
                         "underlying command at current HEAD to obtain "
                         "a fresh witness.")

    emit(witnessed(value))
    return 0 if is_current else 1


# ============== Main ==============


def main() -> int:
    parser = argparse.ArgumentParser(
        prog="leanctx",
        description=("Witness layer for the Lean corpus. Phase 1: hard "
                     "witnesses only. No semantic claim map; no doctrine "
                     "mapping; no promotion readiness."),
    )
    sub = parser.add_subparsers(dest="cmd", required=True)

    sub.add_parser("head", help="Return HEAD SHA + dirty status")

    p_grep = sub.add_parser("grep", help="Literal source search")
    p_grep.add_argument("literal", help="Literal string to search")
    p_grep.add_argument(
        "--scope", choices=["tracked", "worktree"], default="tracked",
        help=("Search scope: 'tracked' (default, git-tracked files only, "
              "at_sha) or 'worktree' (also includes untracked files, "
              "demoted to working_tree_only)."),
    )

    p_module = sub.add_parser("module", help="Resolve module to source path")
    p_module.add_argument("module", help="Module name (dot-separated)")

    p_decl = sub.add_parser("decl", help="Find declaration candidates")
    p_decl.add_argument("decl", help="Declaration name to search")
    p_decl.add_argument(
        "--scope", choices=["tracked", "worktree"], default="tracked",
        help=("Search scope: 'tracked' (default, git-tracked files only, "
              "at_sha) or 'worktree' (also includes untracked files, "
              "demoted to working_tree_only)."),
    )

    p_build = sub.add_parser("build", help="Run lake build + emit receipt")
    p_build.add_argument("module", help="Module name to build")

    p_receipt = sub.add_parser(
        "receipt-valid",
        help="Check receipt currency vs current HEAD",
    )
    p_receipt.add_argument("receipt_file", help="Path to receipt JSON file")

    args = parser.parse_args()

    dispatch = {
        "head": cmd_head,
        "grep": cmd_grep,
        "module": cmd_module,
        "decl": cmd_decl,
        "build": cmd_build,
        "receipt-valid": cmd_receipt_valid,
    }

    try:
        return dispatch[args.cmd](args)
    except KeyboardInterrupt:
        return 130


if __name__ == "__main__":
    sys.exit(main())
