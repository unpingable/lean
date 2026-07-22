#!/usr/bin/env python3
"""Fail-closed qualification for the provisional PJ Tranche C-prime candidate.

This thin policy layer reuses the ratified PJ-A and B-prime verifier.  It adds
the two exact C-prime boundary modules and verifies the B-prime candidate and
ratification ancestry.  It does not implement an owner, context transport, or
generic frontier, and it does not ratify C-prime.
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
BASE_CHECKER_PATH = SCRIPT_DIR / "check-pj-tranche-b-prime.py"
SPEC = importlib.util.spec_from_file_location(
    "pj_tranche_b_prime_checker", BASE_CHECKER_PATH
)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError(f"cannot load ratified PJ-B-prime checker: {BASE_CHECKER_PATH}")
B_PRIME = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(B_PRIME)


PJ_B_PRIME_CANDIDATE = "4e48186cc87249dd5e308e1381345d9758454687"
PJ_B_PRIME_CANDIDATE_TREE = "8a7c6bf30da059dfe22e35750ae114fbb35eeccd"
PJ_B_PRIME_PARENT = "a66918dda9dd32892d6275abaa59229633ab3a07"
PJ_B_PRIME_RATIFICATION = "06856876f7f111ad49a17b6eecba5b46ae238211"
PJ_B_PRIME_RATIFICATION_TREE = "52c09c34aedaf2fcca2a193c0dfb1d82a7d5fa64"


POLICY: dict[str, Any] = copy.deepcopy(B_PRIME.POLICY)
POLICY.update({
    "campaign_id": "pj-tranche-c-prime-2026-07-22",
    "qualification": "PJ/Campaign/TrancheCPrimeQualification.lean",
    "dump": "scripts/PJTrancheCPrimeDeclarationDump.lean",
    "manifest": "PJ/Campaign/tranche-c-prime-declaration-manifest.json",
})
POLICY["modules"].update({
    "PJ.TrancheCPrime.Ownership": {
        "path": "PJ/TrancheCPrime/Ownership.lean",
        "prefix": "PJ.TrancheCPrime.Ownership",
        "direct_imports": [
            "PJ.TrancheBPrime.Instances",
            "PJ.TrancheBPrime.HeldOutStaticRole",
            "ContinuityQualification.Hostile",
        ],
    },
    "PJ.TrancheCPrime.ContextTransport": {
        "path": "PJ/TrancheCPrime/ContextTransport.lean",
        "prefix": "PJ.TrancheCPrime.ContextTransport",
        "direct_imports": [
            "PJ.TrancheBPrime.Instances",
            "PJ.TrancheBPrime.HeldOutStaticRole",
            "Calculi.Scratch.GovernedTransport.Coherence",
            "Calculi.Scratch.GovernedTransport.CoverageRepair",
            "StaticRole.Model.UptakeTransport",
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
            "PJ.TrancheCPrime.Ownership",
            "PJ.TrancheCPrime.ContextTransport",
        ],
    },
    "PJ/Campaign/TrancheCPrimeQualification.lean": {
        "direct_imports": [
            "PJ.TrancheCPrime.Ownership",
            "PJ.TrancheCPrime.ContextTransport",
        ],
    },
}

# The imported checkers share the PJ-A implementation module.  Install one
# policy rather than copy its verifier logic into a third stage script.
B_PRIME.POLICY = POLICY
B_PRIME.BASE.POLICY = POLICY
B_PRIME.BASE.DUMP_SCHEMA = "pj-tranche-c-prime-compiled-declaration-v1"
B_PRIME.BASE.MANIFEST_KIND = "pj-tranche-c-prime-compiled-declarations"


GENERIC_FRONTIER_IDENTIFIER = re.compile(
    r"\b(?:Frontier|GenericFrontier|Remaining|RemainingAfter|Obligations)\b"
)


def require_parent(git: Any, revision: str, expected: str, label: str) -> None:
    actual = git.text("rev-parse", f"{revision}^")
    if actual != expected:
        raise B_PRIME.BASE.CheckError(
            "CONTINUATION_PARENT_DRIFT", f"{label}: {actual}"
        )


def verify_continuation_state(formalization: Path) -> dict[str, Any]:
    inherited = B_PRIME.verify_continuation_state(formalization)
    git = B_PRIME.BASE.Git(formalization.parent)
    head = git.text("rev-parse", "HEAD^{commit}")

    git.require_commit(
        PJ_B_PRIME_CANDIDATE,
        PJ_B_PRIME_CANDIDATE_TREE,
        "PJ-B-prime candidate",
    )
    require_parent(
        git, PJ_B_PRIME_CANDIDATE, PJ_B_PRIME_PARENT, "PJ-B-prime candidate"
    )
    git.require_commit(
        PJ_B_PRIME_RATIFICATION,
        PJ_B_PRIME_RATIFICATION_TREE,
        "PJ-B-prime ratification",
    )
    require_parent(
        git,
        PJ_B_PRIME_RATIFICATION,
        PJ_B_PRIME_CANDIDATE,
        "PJ-B-prime ratification",
    )
    if not git.is_ancestor(PJ_B_PRIME_RATIFICATION, head):
        raise B_PRIME.BASE.CheckError(
            "CONTINUATION_ANCESTRY_DRIFT",
            f"{PJ_B_PRIME_RATIFICATION} is not an ancestor of {head}",
        )

    for relative in (
        "PJ/TrancheCPrime/Ownership.lean",
        "PJ/TrancheCPrime/ContextTransport.lean",
    ):
        path = formalization / relative
        if not path.is_file() or path.is_symlink():
            raise B_PRIME.BASE.CheckError("FORMAL_SOURCE_MISSING", relative)
        code = B_PRIME.BASE.lean_code_without_comments_or_strings(
            path.read_text(encoding="utf-8")
        )
        match = GENERIC_FRONTIER_IDENTIFIER.search(code)
        if match is not None:
            line = code.count("\n", 0, match.start()) + 1
            raise B_PRIME.BASE.CheckError(
                "GENERIC_FRONTIER_RESURRECTED",
                f"{relative}:{line}:{match.group(0)}",
            )

    return {
        **inherited,
        "head": head,
        "pj_b_prime_candidate": PJ_B_PRIME_CANDIDATE,
        "pj_b_prime_ratification": PJ_B_PRIME_RATIFICATION,
    }


def verify(
    formalization: Path, *, skip_build: bool, write_manifest: bool
) -> dict[str, Any]:
    continuation = verify_continuation_state(formalization)
    result = B_PRIME.BASE.verify(
        formalization, skip_build=skip_build, write_manifest=write_manifest
    )
    result.update({
        "result": "PJ-TRANCHE-C-PRIME-QUALIFICATION-PASS",
        "campaign_id": POLICY["campaign_id"],
        "continuation": continuation,
        "generic_frontier": "REJECTED-AND-ABSENT",
        "ownership": "NO-USEFUL-OWNERSHIP-COMMONALITY",
        "context_transport": "CONTEXT-TRANSPORT-NOT-GENERIC",
        "residual_theories": "ONLY-DOMAIN-SPECIFIC-RESIDUAL-THEORIES",
    })
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--formalization",
        type=Path,
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
    except B_PRIME.BASE.CheckError as error:
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
