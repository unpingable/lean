#!/usr/bin/env python3
"""Fail-closed qualification for the provisional PJ Tranche B-prime candidate.

The checker reuses the ratified PJ-A source-pin, import, constructivity, axiom,
and compiled-declaration verifier.  This thin policy layer adds the exact
B-prime modules and authoritative continuation-chain checks.  It deliberately
contains no generic frontier policy and does not ratify the candidate.
"""

from __future__ import annotations

import argparse
import copy
import importlib.util
import json
from pathlib import Path
import re
import sys
from typing import Any


SCRIPT_DIR = Path(__file__).resolve().parent
BASE_CHECKER_PATH = SCRIPT_DIR / "check-pj-tranche-a.py"
SPEC = importlib.util.spec_from_file_location("pj_tranche_a_checker", BASE_CHECKER_PATH)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError(f"cannot load ratified PJ-A checker: {BASE_CHECKER_PATH}")
BASE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(BASE)


PJ_A_CANDIDATE = "d634517fc08205758de59466c97f5998f774dabb"
PJ_A_CANDIDATE_TREE = "c539b62398d30b5d12a40fdffef53eb543305705"
PJ_A_PARENT = "99f3973aca420817ac4eb5a5a1282252326c32e7"
PJ_A_RATIFICATION = "d1fad6efc608b7daf3b8a8f47b7f4cfc5a1c249e"
PJ_A_RATIFICATION_TREE = "706da052cb2dcff572054f686884f92bb43829ad"
PJ_B_FAST_FALSIFICATION = "a66918dda9dd32892d6275abaa59229633ab3a07"
PJ_B_FAST_FALSIFICATION_TREE = "68d7023bfb42a8a08a490ad4419334ccd5b5ca92"


POLICY: dict[str, Any] = copy.deepcopy(BASE.POLICY)
POLICY.update({
    "campaign_id": "pj-tranche-b-prime-2026-07-22",
    "qualification": "PJ/Campaign/TrancheBPrimeQualification.lean",
    "dump": "scripts/PJTrancheBPrimeDeclarationDump.lean",
    "manifest": "PJ/Campaign/tranche-b-prime-declaration-manifest.json",
})
POLICY["modules"].update({
    "PJ.TrancheBPrime.AntiMinting": {
        "path": "PJ/TrancheBPrime/AntiMinting.lean",
        "prefix": "PJ.TrancheBPrime",
        "direct_imports": ["PJ.Core"],
    },
    "PJ.TrancheBPrime.Instances": {
        "path": "PJ/TrancheBPrime/Instances.lean",
        "prefix": "PJ.TrancheBPrime.Instances",
        "direct_imports": [
            "PJ.TrancheBPrime.AntiMinting",
            "PJ.Instances.GovernedTransport",
            "PJ.Instances.ExecutionCustody",
            "PJ.Instances.SomeoneContinuity",
        ],
    },
    "PJ.TrancheBPrime.HeldOutStaticRole": {
        "path": "PJ/TrancheBPrime/HeldOutStaticRole.lean",
        "prefix": "PJ.TrancheBPrime.HeldOutStaticRole",
        "direct_imports": [
            "PJ.TrancheBPrime.AntiMinting",
            "PJ.HeldOut.StaticRole",
        ],
    },
})
POLICY["auxiliary_lean"] = {
    "PJ.lean": {
        "direct_imports": [
            "PJ.Core",
            "PJ.Hostile",
            "PJ.Instances.GovernedTransport",
            "PJ.Instances.ExecutionCustody",
            "PJ.Instances.SomeoneContinuity",
            "PJ.HeldOut.StaticRole",
            "PJ.TrancheBPrime.AntiMinting",
            "PJ.TrancheBPrime.Instances",
            "PJ.TrancheBPrime.HeldOutStaticRole",
        ],
    },
    "PJ/Campaign/TrancheBPrimeQualification.lean": {
        "direct_imports": [
            "PJ.TrancheBPrime.AntiMinting",
            "PJ.TrancheBPrime.Instances",
            "PJ.TrancheBPrime.HeldOutStaticRole",
        ],
    },
}

BASE.POLICY = POLICY
BASE.DUMP_SCHEMA = "pj-tranche-b-prime-compiled-declaration-v1"
BASE.MANIFEST_KIND = "pj-tranche-b-prime-compiled-declarations"


GENERIC_FRONTIER_IDENTIFIER = re.compile(
    r"\b(?:Frontier|GenericFrontier|Remaining|RemainingAfter|Obligations)\b"
)


def require_parent(git: Any, revision: str, expected: str, label: str) -> None:
    actual = git.text("rev-parse", f"{revision}^")
    if actual != expected:
        raise BASE.CheckError("CONTINUATION_PARENT_DRIFT", f"{label}: {actual}")


def verify_continuation_state(formalization: Path) -> dict[str, str]:
    outer = formalization.parent
    git = BASE.Git(outer)
    head = git.text("rev-parse", "HEAD^{commit}")
    branch = git.text("branch", "--show-current")
    if branch != "pj-cross-calculus-candidate":
        raise BASE.CheckError("CONTINUATION_BRANCH_DRIFT", branch)

    git.require_commit(PJ_A_CANDIDATE, PJ_A_CANDIDATE_TREE, "PJ-A candidate")
    require_parent(git, PJ_A_CANDIDATE, PJ_A_PARENT, "PJ-A candidate")
    git.require_commit(
        PJ_A_RATIFICATION, PJ_A_RATIFICATION_TREE, "PJ-A ratification"
    )
    require_parent(git, PJ_A_RATIFICATION, PJ_A_CANDIDATE, "PJ-A ratification")
    git.require_commit(
        PJ_B_FAST_FALSIFICATION,
        PJ_B_FAST_FALSIFICATION_TREE,
        "PJ-B fast-falsification record",
    )
    require_parent(
        git,
        PJ_B_FAST_FALSIFICATION,
        PJ_A_RATIFICATION,
        "PJ-B fast-falsification record",
    )
    if not git.is_ancestor(PJ_B_FAST_FALSIFICATION, head):
        raise BASE.CheckError(
            "CONTINUATION_ANCESTRY_DRIFT",
            f"{PJ_B_FAST_FALSIFICATION} is not an ancestor of {head}",
        )

    rejected = formalization / "PJ/TrancheB"
    rejected_status = git.text(
        "status", "--porcelain=v1", "--untracked-files=all", "--",
        "formalization/PJ/TrancheB",
    )
    rejected_contents = list(rejected.iterdir()) if rejected.is_dir() else []
    if rejected.is_file() or rejected.is_symlink() or rejected_contents or rejected_status:
        raise BASE.CheckError(
            "GENERIC_FRONTIER_RESURRECTED",
            rejected_status or ", ".join(str(path) for path in rejected_contents)
            or str(rejected),
        )

    for relative in (
        "PJ/TrancheBPrime/AntiMinting.lean",
        "PJ/TrancheBPrime/Instances.lean",
        "PJ/TrancheBPrime/HeldOutStaticRole.lean",
    ):
        path = formalization / relative
        if not path.is_file() or path.is_symlink():
            raise BASE.CheckError("FORMAL_SOURCE_MISSING", relative)
        code = BASE.lean_code_without_comments_or_strings(
            path.read_text(encoding="utf-8")
        )
        match = GENERIC_FRONTIER_IDENTIFIER.search(code)
        if match is not None:
            line = code.count("\n", 0, match.start()) + 1
            raise BASE.CheckError(
                "GENERIC_FRONTIER_RESURRECTED",
                f"{relative}:{line}:{match.group(0)}",
            )

    return {
        "branch": branch,
        "head": head,
        "pj_a_candidate": PJ_A_CANDIDATE,
        "pj_a_ratification": PJ_A_RATIFICATION,
        "pj_b_fast_falsification": PJ_B_FAST_FALSIFICATION,
    }


def verify(
    formalization: Path, *, skip_build: bool, write_manifest: bool
) -> dict[str, Any]:
    continuation = verify_continuation_state(formalization)
    result = BASE.verify(
        formalization, skip_build=skip_build, write_manifest=write_manifest
    )
    result.update({
        "result": "PJ-TRANCHE-B-PRIME-QUALIFICATION-PASS",
        "campaign_id": POLICY["campaign_id"],
        "continuation": continuation,
        "generic_frontier": "REJECTED-AND-ABSENT",
    })
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--formalization", type=Path,
        default=Path(__file__).resolve().parent.parent,
    )
    parser.add_argument("--skip-build", action="store_true")
    parser.add_argument("--write-manifest", action="store_true")
    args = parser.parse_args()
    try:
        result = verify(
            args.formalization.resolve(),
            skip_build=args.skip_build,
            write_manifest=args.write_manifest,
        )
    except BASE.CheckError as error:
        print(
            json.dumps(
                {"result": "FAIL", "code": error.code, "message": error.message},
                sort_keys=True,
            ),
            file=sys.stderr,
        )
        return 1
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
