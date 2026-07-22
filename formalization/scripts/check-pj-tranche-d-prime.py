#!/usr/bin/env python3
"""Fail-closed qualification for the provisional PJ Tranche D-prime audit.

This thin policy layer reuses the ratified PJ-A/B-prime/C-prime verifier.  It
adds only the two D-prime hostile/out-of-sample modules, verifies the exact
C-prime candidate and ratification ancestry, and pins the independent public
Admissibility source used out of sample.  It does not ratify a final PJ label.
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
BASE_CHECKER_PATH = SCRIPT_DIR / "check-pj-tranche-c-prime.py"
SPEC = importlib.util.spec_from_file_location(
    "pj_tranche_c_prime_checker", BASE_CHECKER_PATH
)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError(f"cannot load ratified PJ-C-prime checker: {BASE_CHECKER_PATH}")
C_PRIME = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(C_PRIME)


PJ_C_PRIME_CANDIDATE = "7bddca0411b1af93a76923691eb1d324a3f92856"
PJ_C_PRIME_CANDIDATE_TREE = "6a97636eebdf1ddfd69a0572307d0e8b548b50d4"
PJ_C_PRIME_PARENT = "06856876f7f111ad49a17b6eecba5b46ae238211"
PJ_C_PRIME_RATIFICATION = "c2d011779ea1aa579cb199d5869b34b19b2180e6"
PJ_C_PRIME_RATIFICATION_TREE = "5a8b5bb6d540c9ae777292d9a6ab02ac9f2dab07"

ADMISSIBILITY_REVISION = "9dca58f4587a4a4f5b724662b176af8de3040c04"
ADMISSIBILITY_TREE = "7e2b27939bafe7a214085112af2777e395b1b94f"
ADMISSIBILITY_PATH = "LeanProofs/Admissibility/Calculus/Core.lean"
ADMISSIBILITY_BLOB = "961f4d2a1ea7c5d9236338dedf42ded6481d1c3e"
ADMISSIBILITY_SHA256 = (
    "13f0f8164ff6c9de6b9cfb05053fc1bed58aeb7d8c3f2289df5d69cb32dd5b7c"
)


POLICY: dict[str, Any] = copy.deepcopy(C_PRIME.POLICY)
POLICY.update({
    "campaign_id": "pj-tranche-d-prime-2026-07-22",
    "qualification": "PJ/Campaign/TrancheDPrimeQualification.lean",
    "dump": "scripts/PJTrancheDPrimeDeclarationDump.lean",
    "manifest": "PJ/Campaign/tranche-d-prime-declaration-manifest.json",
})
POLICY["modules"].update({
    "PJ.TrancheDPrime.CollapseHostiles": {
        "path": "PJ/TrancheDPrime/CollapseHostiles.lean",
        "prefix": "PJ.TrancheDPrime.CollapseHostiles",
        "direct_imports": ["PJ.TrancheBPrime.AntiMinting"],
    },
    "PJ.TrancheDPrime.OutOfSampleAdmissibility": {
        "path": "PJ/TrancheDPrime/OutOfSampleAdmissibility.lean",
        "prefix": "PJ.TrancheDPrime.OutOfSampleAdmissibility",
        "direct_imports": [
            "PJ.TrancheBPrime.AntiMinting",
            "LeanProofs.Admissibility.Calculus.Core",
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
            "PJ.TrancheDPrime.CollapseHostiles",
            "PJ.TrancheDPrime.OutOfSampleAdmissibility",
        ],
    },
    "PJ/Campaign/TrancheDPrimeQualification.lean": {
        "direct_imports": [
            "PJ.TrancheDPrime.CollapseHostiles",
            "PJ.TrancheDPrime.OutOfSampleAdmissibility",
        ],
    },
}

# All imported wrappers share the original PJ-A implementation module. Install
# one exact policy instead of duplicating declaration/source verification.
C_PRIME.POLICY = POLICY
C_PRIME.B_PRIME.POLICY = POLICY
C_PRIME.B_PRIME.BASE.POLICY = POLICY
C_PRIME.B_PRIME.BASE.DUMP_SCHEMA = (
    "pj-tranche-d-prime-compiled-declaration-v1"
)
C_PRIME.B_PRIME.BASE.MANIFEST_KIND = (
    "pj-tranche-d-prime-compiled-declarations"
)

# The inherited verifier knows the four PJ-A sources.  Extend only the
# manifest inputs for D-prime so the out-of-sample dependency is serialized in
# the same canonical source-pins object after it is independently verified.
BASE = C_PRIME.B_PRIME.BASE
ORIGINAL_DECLARATION_MANIFEST_BYTES = BASE.declaration_manifest_bytes
ORIGINAL_VALIDATE_MANIFEST = BASE.validate_manifest


def with_admissibility_pin(source_pins: dict[str, Any]) -> dict[str, Any]:
    return {
        **source_pins,
        "admissibility_calculus": {
            "revision": ADMISSIBILITY_REVISION,
            "tree": ADMISSIBILITY_TREE,
            "path": ADMISSIBILITY_PATH,
            "blob": ADMISSIBILITY_BLOB,
            "sha256": ADMISSIBILITY_SHA256,
        },
    }


def declaration_manifest_bytes(
    dump_output: str,
    source_files: dict[str, dict[str, str]],
    source_pins: dict[str, Any],
) -> tuple[bytes, dict[str, Any]]:
    return ORIGINAL_DECLARATION_MANIFEST_BYTES(
        dump_output, source_files, with_admissibility_pin(source_pins)
    )


def validate_manifest(
    document: dict[str, Any],
    source_files: dict[str, dict[str, str]],
    source_pins: dict[str, Any],
) -> None:
    ORIGINAL_VALIDATE_MANIFEST(
        document, source_files, with_admissibility_pin(source_pins)
    )


BASE.declaration_manifest_bytes = declaration_manifest_bytes
BASE.validate_manifest = validate_manifest


GENERIC_REINTRODUCTION = re.compile(
    r"\b(?:structure|class|inductive|def|abbrev)\s+"
    r"(?:Frontier|GenericFrontier|Remaining|RemainingAfter|Obligations|"
    r"Owner|Institution|ContextTransport|Residual|Residue|Debt)\b"
)


def require_parent(git: Any, revision: str, expected: str, label: str) -> None:
    actual = git.text("rev-parse", f"{revision}^")
    if actual != expected:
        raise C_PRIME.B_PRIME.BASE.CheckError(
            "CONTINUATION_PARENT_DRIFT", f"{label}: {actual}"
        )


def verify_public_admissibility(formalization: Path) -> dict[str, str]:
    base = C_PRIME.B_PRIME.BASE
    public_root = formalization.parent.parent / "lean"
    git = base.Git(public_root)
    git.require_commit(
        ADMISSIBILITY_REVISION, ADMISSIBILITY_TREE, "public Admissibility source"
    )
    oid, frozen = git.blob_at(ADMISSIBILITY_REVISION, ADMISSIBILITY_PATH)
    if oid != ADMISSIBILITY_BLOB or base.sha256(frozen) != ADMISSIBILITY_SHA256:
        raise base.CheckError("ADMISSIBILITY_SOURCE_DRIFT", ADMISSIBILITY_PATH)
    base.require_file_digest(
        public_root, ADMISSIBILITY_PATH, ADMISSIBILITY_SHA256
    )
    base.require_clean_path(git, ADMISSIBILITY_PATH)
    return {
        "revision": ADMISSIBILITY_REVISION,
        "tree": ADMISSIBILITY_TREE,
        "path": ADMISSIBILITY_PATH,
        "blob": ADMISSIBILITY_BLOB,
        "sha256": ADMISSIBILITY_SHA256,
    }


def verify_continuation_state(formalization: Path) -> dict[str, Any]:
    inherited = C_PRIME.verify_continuation_state(formalization)
    base = C_PRIME.B_PRIME.BASE
    git = base.Git(formalization.parent)
    head = git.text("rev-parse", "HEAD^{commit}")

    git.require_commit(
        PJ_C_PRIME_CANDIDATE,
        PJ_C_PRIME_CANDIDATE_TREE,
        "PJ-C-prime candidate",
    )
    require_parent(
        git, PJ_C_PRIME_CANDIDATE, PJ_C_PRIME_PARENT, "PJ-C-prime candidate"
    )
    git.require_commit(
        PJ_C_PRIME_RATIFICATION,
        PJ_C_PRIME_RATIFICATION_TREE,
        "PJ-C-prime ratification",
    )
    require_parent(
        git,
        PJ_C_PRIME_RATIFICATION,
        PJ_C_PRIME_CANDIDATE,
        "PJ-C-prime ratification",
    )
    if not git.is_ancestor(PJ_C_PRIME_RATIFICATION, head):
        raise base.CheckError(
            "CONTINUATION_ANCESTRY_DRIFT",
            f"{PJ_C_PRIME_RATIFICATION} is not an ancestor of {head}",
        )

    for relative in (
        "PJ/TrancheDPrime/CollapseHostiles.lean",
        "PJ/TrancheDPrime/OutOfSampleAdmissibility.lean",
    ):
        path = formalization / relative
        if not path.is_file() or path.is_symlink():
            raise base.CheckError("FORMAL_SOURCE_MISSING", relative)
        code = base.lean_code_without_comments_or_strings(
            path.read_text(encoding="utf-8")
        )
        match = GENERIC_REINTRODUCTION.search(code)
        if match is not None:
            line = code.count("\n", 0, match.start()) + 1
            raise base.CheckError(
                "REJECTED_GENERIC_STRUCTURE_REINTRODUCED",
                f"{relative}:{line}:{match.group(0)}",
            )

    return {
        **inherited,
        "head": head,
        "pj_c_prime_candidate": PJ_C_PRIME_CANDIDATE,
        "pj_c_prime_ratification": PJ_C_PRIME_RATIFICATION,
    }


def verify(
    formalization: Path, *, skip_build: bool, write_manifest: bool
) -> dict[str, Any]:
    continuation = verify_continuation_state(formalization)
    admissibility = verify_public_admissibility(formalization)
    result = C_PRIME.B_PRIME.BASE.verify(
        formalization, skip_build=skip_build, write_manifest=write_manifest
    )
    result["sources"] = {
        **result["sources"],
        "admissibility_calculus": admissibility,
    }
    result.update({
        "result": "PJ-TRANCHE-D-PRIME-QUALIFICATION-PASS",
        "campaign_id": POLICY["campaign_id"],
        "continuation": continuation,
        "out_of_sample_admissibility": admissibility,
        "generic_frontier": "REJECTED-AND-ABSENT",
        "ownership": "NO-USEFUL-OWNERSHIP-COMMONALITY",
        "context_transport": "CONTEXT-TRANSPORT-NOT-GENERIC",
        "residual_theories": "ONLY-DOMAIN-SPECIFIC-RESIDUAL-THEORIES",
        "candidate_classification": "ATLAS-CANDIDATE",
        "closest_alternative": "ARCHIPELAGO-CANDIDATE",
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
    except C_PRIME.B_PRIME.BASE.CheckError as error:
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
