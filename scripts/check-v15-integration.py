#!/usr/bin/env python3
"""Fail closed on the bounded V15 public integration invariants."""

from __future__ import annotations

import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
TRANSFER = "d1e2d18ffc6e27365ec890a6ae2439c87688b350"
TRANSFER_TREE = "fbd5a31ec5e2432759db45d2359c3e3f74198b52"
TRANSFER_MANIFEST_SHA = (
    "05a29867a8c9c24996f9a1b975749a61379f32b5b8cdebc9a1100504147d6268"
)
FINAL_VERDICT_SHA = (
    "3efad909f66b2caed45e57606c3c879ad877e902606d4046e057eff7942002aa"
)

# Exact post-V15 public-evidence additions. These paths are not part of the
# V15 surface and are excluded only from the repository-wide LeanProofs freeze
# below. Every other added or changed path under LeanProofs still fails that
# freeze.
POST_V15_ISOLATED_PUBLIC_EVIDENCE = (
    "LeanProofs/GovernedTransitionBoundaries.lean",
    "LeanProofs/GovernedTransitionBoundaries/Core.lean",
    "LeanProofs/GovernedTransitionBoundariesEvidence.lean",
    "LeanProofs/GovernedTransitionBoundariesEvidence/ContextBoundary.lean",
    "LeanProofs/GovernedTransitionBoundariesEvidence/FiniteRepresentation.lean",
    "LeanProofs/GovernedTransitionBoundariesEvidence/GroundingBoundary.lean",
    "LeanProofs/GovernedTransitionBoundariesEvidence/HistoricalBoundary.lean",
    "LeanProofs/GovernedTransitionBoundariesEvidence/JurisdictionBoundary.lean",
    "LeanProofs/GovernedTransitionBoundariesEvidence/Qualification.lean",
    "LeanProofs/GovernedTransitionBoundariesEvidence/RealizabilityBoundary.lean",
)
# Track A (the frozen Inquiry/Preparation comparison-only neighbors) lives in
# the private research repository by design — those sources were deliberately
# not transferred. The commit, tree, and blob ids pinned below are the
# committed public receipt of that freeze; Git object ids are content
# addresses, so drift in the private repo cannot be hidden from a later
# workstation re-attestation. When the private repository is unavailable
# (public CI runners), the pins still stand as the recorded freeze and the
# live re-attestation is reported as skipped rather than silently passed.
# Override the location with V15_TRACK_A_REPO.
TRACK_A_COMMIT = "cfeffc950e795752ad1928a314890185c0cda723"
TRACK_A_TREE = "4d9de55c0d19f3984dc486ac124b2e4f2a7e1e11"
TRACK_A_REPO = Path(
    os.environ.get("V15_TRACK_A_REPO", "/home/jbeck/git/skunkworks")
)

PJ_MANIFESTS = (
    (
        "formalization/PJ/Campaign/declaration-manifest.json",
        "formalization/scripts/PJTrancheADeclarationDump.lean",
        292,
    ),
    (
        "formalization/PJ/Campaign/tranche-b-prime-declaration-manifest.json",
        "formalization/scripts/PJTrancheBPrimeDeclarationDump.lean",
        514,
    ),
    (
        "formalization/PJ/Campaign/tranche-c-prime-declaration-manifest.json",
        "formalization/scripts/PJTrancheCPrimeDeclarationDump.lean",
        553,
    ),
    (
        "formalization/PJ/Campaign/tranche-d-prime-declaration-manifest.json",
        "formalization/scripts/PJTrancheDPrimeDeclarationDump.lean",
        591,
    ),
)

FROZEN_MANIFESTS = (
    "formalization/docs/someone-continuity-qualification-2026-07-22/"
    "declaration-manifest.json",
    *(item[0] for item in PJ_MANIFESTS),
    "formalization/PJ/Campaign/SOURCE-MANIFEST.tsv",
    "formalization/docs/someone-continuity-qualification-2026-07-22/"
    "source-manifest.tsv",
)

TRACK_A_BLOBS = {
    "formalization/Calculi/Scratch/Campaigns/V15Frontier.lean": (
        "0238f9a2a9c2a1a17254c4b359444ca743becbf2"
    ),
    "formalization/Calculi/Scratch/V15Frontier/Inquiry/Core.lean": (
        "6724fa9c83f03d55620caca52e8eb7aea947e5bc"
    ),
    "formalization/Calculi/Scratch/V15Frontier/Inquiry/Fixtures.lean": (
        "79e5673322934c5e740d3d1741bcd745af37e22b"
    ),
    "formalization/Calculi/Scratch/V15Frontier/Preparation/Core.lean": (
        "9dfd6f18a74de35755f7bacc2fe1dcaa9ebdf4db"
    ),
    "formalization/Calculi/Scratch/V15Frontier/Preparation/"
    "DeterministicRefinement.lean": (
        "3b4e134705cc0f85d1ba7d3b0aa7d30059e8f373"
    ),
    "formalization/Calculi/Scratch/V15Frontier/Preparation/Audit.lean": (
        "61c2f748ccf77801577bf465539e9037d71744e6"
    ),
    "formalization/V15_INQUIRY_ABSTRACT_CANDIDATE_2026-07-18.md": (
        "71f5812caa5d4df9f8d0ec4915f0728d7af7f8d3"
    ),
    "formalization/V15_PREPARATION_ABSTRACT_CANDIDATE_2026-07-18.md": (
        "79a1a81c30a344fb0ecac3d5ac1cee0737059b17"
    ),
    "formalization/V15_TRIANGULATION_RECONCILIATION_GATE_2026-07-18.md": (
        "f6a7fff47d8a087cb190a77273cc7365811e4114"
    ),
}

PATH_RENAMES = {
    "formalization/PJ/Instances/SomeoneContinuity.lean": (
        "formalization/PJ/Instances/ContinuityAdmission.lean"
    ),
    "formalization/ContinuityQualification/Core.lean": (
        "formalization/Continuity/Admission/Qualification/Core.lean"
    ),
    "formalization/ContinuityQualification/Hostile.lean": (
        "formalization/Continuity/Admission/Qualification/Hostile.lean"
    ),
    "formalization/ContinuityQualification.lean": (
        "formalization/Continuity/Admission/Qualification.lean"
    ),
    "formalization/ContinuityQualification/Campaign/Qualification.lean": (
        "formalization/Continuity/Admission/Qualification/Campaign.lean"
    ),
    "formalization/scripts/SomeoneContinuityDeclarationDump.lean": (
        "formalization/scripts/ContinuityAdmissionDeclarationDump.lean"
    ),
}

SAME_PATH_RENAMES = (
    "formalization/PJ/Campaign/TrancheAQualification.lean",
    "formalization/PJ/Campaign/TrancheBPrimeQualification.lean",
    "formalization/PJ/Campaign/TrancheCPrimeQualification.lean",
    "formalization/PJ/TrancheBPrime/Instances.lean",
    "formalization/PJ/TrancheCPrime/ContextTransport.lean",
    "formalization/PJ/TrancheCPrime/Ownership.lean",
    "formalization/scripts/PJTrancheADeclarationDump.lean",
    "formalization/scripts/PJTrancheBPrimeDeclarationDump.lean",
    "formalization/scripts/PJTrancheCPrimeDeclarationDump.lean",
    "formalization/scripts/PJTrancheDPrimeDeclarationDump.lean",
)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def run(*args: str, cwd: Path = ROOT) -> subprocess.CompletedProcess[bytes]:
    return subprocess.run(
        args, cwd=cwd, check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE
    )


def git_bytes(revision: str, path: str) -> bytes:
    return run("git", "show", f"{revision}:{path}").stdout


def renamed_text(data: bytes) -> bytes:
    replacements = (
        (b"SomeoneContinuityQualification", b"Continuity.Admission.Qualification"),
        (b"ContinuityQualification.Core", b"Continuity.Admission.Qualification.Core"),
        (b"ContinuityQualification.Hostile", b"Continuity.Admission.Qualification.Hostile"),
        (b"PJ.Instances.SomeoneContinuity", b"PJ.Instances.ContinuityAdmission"),
        (b"SomeoneContinuity", b"ContinuityAdmission"),
        (b"Someone.", b"Continuity.Admission."),
        (b"`Someone,", b"`Continuity.Admission,"),
        (b"open Someone\n", b"open Continuity.Admission\n"),
        (b"import Someone\n", b"import Continuity.Admission\n"),
        (b"import ContinuityQualification\n", b"import Continuity.Admission.Qualification\n"),
        (
            b"Isolated aggregate for the bounded Someone continuity-admission",
            b"Isolated aggregate for the bounded Continuity.Admission",
        ),
        (
            b"Compiled declaration census for the bounded Someone -> Continuity",
            b"Compiled declaration census for the bounded Continuity.Admission",
        ),
    )
    for old, new in replacements:
        data = data.replace(old, new)
    return data


def old_name(value: str) -> str:
    replacements = (
        (
            "PJ.TrancheCPrime.ContextTransport.ContinuityAdmission",
            "PJ.TrancheCPrime.ContextTransport.SomeoneContinuity",
        ),
        (
            "PJ.TrancheCPrime.Ownership.ContinuityAdmission",
            "PJ.TrancheCPrime.Ownership.SomeoneContinuity",
        ),
        (
            "PJ.TrancheBPrime.Instances.ContinuityAdmission",
            "PJ.TrancheBPrime.Instances.SomeoneContinuity",
        ),
        ("PJ.Instances.ContinuityAdmission", "PJ.Instances.SomeoneContinuity"),
        ("Continuity.Admission.Qualification", "SomeoneContinuityQualification"),
        ("Continuity.Admission", "Someone"),
    )
    for new, old in replacements:
        value = value.replace(new, old)
    return value


def verify_source_rewrites() -> None:
    for old_path, new_path in PATH_RENAMES.items():
        expected = renamed_text(git_bytes(TRANSFER, old_path))
        actual = (ROOT / new_path).read_bytes()
        if actual != expected:
            raise ValueError(f"source rewrite exceeded rename allowance: {new_path}")
    for path in SAME_PATH_RENAMES:
        expected = renamed_text(git_bytes(TRANSFER, path))
        if (ROOT / path).read_bytes() != expected:
            raise ValueError(f"source rewrite exceeded rename allowance: {path}")


def verify_frozen_manifests() -> None:
    for path in FROZEN_MANIFESTS:
        if (ROOT / path).read_bytes() != git_bytes(TRANSFER, path):
            raise ValueError(f"frozen campaign manifest changed: {path}")


def verify_pj_declarations() -> tuple[int, int]:
    declarations = 0
    axiom_bearing = 0
    for manifest_path, dump_path, expected_count in PJ_MANIFESTS:
        manifest = json.loads((ROOT / manifest_path).read_text())
        completed = run("lake", "env", "lean", dump_path)
        public = [json.loads(line) for line in completed.stdout.splitlines()]
        public_by_old_name = {old_name(item["name"]): item for item in public}
        expected = manifest["declarations"]
        if len(expected) != expected_count or len(public) != expected_count:
            raise ValueError(f"declaration count drift: {manifest_path}")
        if len(public_by_old_name) != expected_count:
            raise ValueError(f"duplicate declaration after rename: {dump_path}")
        for old in expected:
            current = public_by_old_name.pop(old["name"], None)
            if current is None:
                raise ValueError(f"missing declaration after rename: {old['name']}")
            if current["kind"] != old["kind"]:
                raise ValueError(f"declaration kind drift: {old['name']}")
            if old_name(current["module"]) != old["source_module"]:
                raise ValueError(f"declaration module drift: {old['name']}")
            if [old_name(item) for item in current["axioms"]] != old[
                "normalized_axioms"
            ]:
                raise ValueError(f"axiom footprint drift: {old['name']}")
            if (current["value"] is None) != (old["normalized_value_sha256"] is None):
                raise ValueError(f"proof/value presence drift: {old['name']}")
        if public_by_old_name:
            raise ValueError(f"unexpected declarations after rename: {dump_path}")
        declarations += expected_count
        axiom_bearing += manifest["counts"]["axiom_bearing"]
    return declarations, axiom_bearing


def verify_track_a() -> str:
    if not (TRACK_A_REPO / ".git").exists() and not (TRACK_A_REPO / "HEAD").exists():
        return (
            "Track A freeze pinned "
            f"({TRACK_A_COMMIT[:12]}, {len(TRACK_A_BLOBS)} blobs); private-source "
            "re-attestation skipped (research repository unavailable)"
        )
    tree = run(
        "git", "-C", str(TRACK_A_REPO), "rev-parse", f"{TRACK_A_COMMIT}^{{tree}}"
    ).stdout.decode().strip()
    if tree != TRACK_A_TREE:
        raise ValueError("Track A freeze tree drift")
    for path, expected in TRACK_A_BLOBS.items():
        line = run(
            "git", "-C", str(TRACK_A_REPO), "ls-tree", TRACK_A_COMMIT, "--", path
        ).stdout.decode().strip()
        fields = line.split()
        if len(fields) < 3 or fields[2] != expected:
            raise ValueError(f"Track A frozen blob drift: {path}")
    return "Track A freeze re-attested against the research repository"


def verify_boundaries() -> None:
    transfer_tree = run("git", "rev-parse", f"{TRANSFER}^{{tree}}").stdout.decode().strip()
    if transfer_tree != TRANSFER_TREE:
        raise ValueError("ratified transfer tree drift")
    if run("git", "merge-base", "--is-ancestor", TRANSFER, "HEAD").returncode != 0:
        raise ValueError("ratified transfer is not an ancestor")
    if sha256((ROOT / "docs/V15-PUBLIC-TRANSFER-MANIFEST.tsv").read_bytes()) != (
        TRANSFER_MANIFEST_SHA
    ):
        raise ValueError("transfer manifest digest drift")
    verdict = ROOT / "formalization/PJ/Campaign/PJ-D-PRIME-OPERATOR-VERDICT_2026-07-22.md"
    if sha256(verdict.read_bytes()) != FINAL_VERDICT_SHA:
        raise ValueError("final PJ verdict record drift")
    required = (
        "RATIFY-PJ-D: ATLAS",
        "FRONTIER-NOT-COMPOSITIONAL",
        "NO-USEFUL-OWNERSHIP-COMMONALITY",
        "CONTEXT-TRANSPORT-NOT-GENERIC",
        "ONLY-DOMAIN-SPECIFIC-RESIDUAL-THEORIES",
    )
    verdict_text = verdict.read_text()
    if any(item not in verdict_text for item in required):
        raise ValueError("final PJ classification text drift")
    freeze = subprocess.run(
        (
            "git", "diff", "--quiet", TRANSFER, "HEAD", "--", "LeanProofs",
            *(
                f":(exclude,top){path}"
                for path in POST_V15_ISOLATED_PUBLIC_EVIDENCE
            ),
        ),
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if freeze.returncode != 0:
        raise ValueError("existing public source calculus drift")
    if (ROOT / "someone/Someone.lean").exists():
        raise ValueError("duplicate historical Someone implementation remains")
    if (ROOT / "formalization/PJ/TrancheB").exists():
        raise ValueError("rejected PJ frontier module reappeared")
    if list((ROOT / "formalization/StaticRole").rglob("*R4*")):
        raise ValueError("StaticRole R4 path appeared")


def main() -> int:
    try:
        verify_boundaries()
        verify_frozen_manifests()
        verify_source_rewrites()
        declarations, axiom_bearing = verify_pj_declarations()
        track_a_mode = verify_track_a()
        run("python3", "scripts/check-v15-continuity-rename.py")
    except (OSError, ValueError, subprocess.CalledProcessError, json.JSONDecodeError) as error:
        print(f"FAIL: V15 integration verification: {error}", file=sys.stderr)
        return 1
    print(
        "PASS — V15 integration preserves 4 PJ manifests "
        f"({declarations} cumulative declarations, {axiom_bearing} cumulative "
        "axiom-bearing entries), the 1,005-declaration Continuity correspondence, "
        f"source pins, and final ATLAS verdict; {track_a_mode}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
