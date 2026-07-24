#!/usr/bin/env python3
"""Generate and verify the V15 public qualification declaration footprint."""

from __future__ import annotations

import argparse
import collections
import hashlib
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
INTEGRATION = "1f0e0208584e0f61fe49353dd0fc6b4775e22e00"
FOOTPRINT = ROOT / "docs/V15-PUBLIC-DECLARATION-FOOTPRINT.json"
PATH_MANIFEST = ROOT / "docs/V15-RELEASE-CANDIDATE-PATHS.tsv"
CONTINUITY_MANIFEST = (
    ROOT
    / "formalization/docs/someone-continuity-qualification-2026-07-22"
    / "declaration-manifest.json"
)
PJ_MANIFEST = (
    ROOT / "formalization/PJ/Campaign/tranche-d-prime-declaration-manifest.json"
)
STATIC_TEMPLATE = ROOT / "formalization/scripts/PJTrancheDPrimeDeclarationDump.lean"

# The release-candidate path manifest is a frozen receipt for the ratified
# candidate. Later presentation-only review may edit these reader-facing files
# without rewriting that historical manifest.
POST_CANDIDATE_PRESENTATION_PATHS = {
    "WHAT-THIS-IS.md",
    "WHAT-THIS-PROVES.md",
    "docs/PLAIN-LANGUAGE-SUMMARY.md",
    "docs/V15-PUBLIC-INDEX.md",
    "docs/V15-PRESENTATION-SEMANTIC-AUDIT_2026-07-22.md",
    "docs/calculus/README.md",
}

# Agent operating process, not a public claim surface. Doctrine edits here do
# not touch the ratified candidate's Lean sources, receipts, or manifests.
POST_CANDIDATE_PROCESS_PATHS = {
    "AGENTS.md",
}

STATIC_MODULES = (
    "StaticRole.Core.CausalBase",
    "StaticRole.Core.Centers",
    "StaticRole.Core.Roles",
    "StaticRole.Information.Records",
    "StaticRole.Information.Forecasts",
    "StaticRole.Information.Layer",
    "StaticRole.Representation.Layer",
    "StaticRole.Representation.RoleEncoding",
    "StaticRole.Representation.Succession",
    "StaticRole.Representation.SelfReference",
    "StaticRole.Representation.DeSeProjection",
    "StaticRole.Countermodels.DependencyChain",
    "StaticRole.Countermodels.RoleHierarchy",
    "StaticRole.Countermodels.Provenance",
    "StaticRole.Countermodels.CoherenceHostiles",
    "StaticRole.Functional.Uptake",
    "StaticRole.Functional.Dependence",
    "StaticRole.Countermodels.UptakeHostiles",
    "StaticRole.Theorems.ExpansionIndependence",
    "StaticRole.Theorems.UptakeIndependence",
    "StaticRole.Model.Expansion",
    "StaticRole.Model.Isomorphism",
    "StaticRole.Model.Transport",
    "StaticRole.Model.UptakeIsomorphism",
    "StaticRole.Model.UptakeTransport",
)

REPRESENTATIVE_COLLAPSES = (
    "bridge/target inhabitant without receipt",
    "target truth without entitlement",
    "wrong subject receipt",
    "wrong context receipt",
    "wrong bridge receipt",
    "frontier record projection",
    "owner as empty label",
    "context transport as trivial identity",
    "StaticRole wrong wiring",
    "Continuity same-name without admission",
    "Execution attempt without commit",
    "GT projection without runtime correspondence",
)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def run(*args: str) -> subprocess.CompletedProcess[bytes]:
    return subprocess.run(
        args, cwd=ROOT, check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE
    )


def static_dump_source() -> str:
    template = STATIC_TEMPLATE.read_text()
    tail = template[template.index("def canonicalLevelParamName") :]
    tail = tail.replace(
        "_pj_tranche_d_prime_universe", "_v15_static_role_universe"
    ).replace(
        '"selected PJ module is absent: {moduleName}"',
        '"selected StaticRole module is absent: {moduleName}"',
    ).replace(
        '"pj-tranche-d-prime-compiled-declaration-v1"',
        '"v15-static-role-compiled-declaration-v1"',
    ).replace(
        "end PJTrancheDPrimeDeclarationDump", "end V15StaticRoleDeclarationDump"
    )
    selected = ",\n  ".join(f"`{module}" for module in STATIC_MODULES)
    return (
        "import Lean\n"
        "import Lean.Util.CollectAxioms\n"
        "import StaticRole\n\n"
        "open Lean\n\n"
        "namespace V15StaticRoleDeclarationDump\n\n"
        f"def selectedModules : Array Name := #[\n  {selected}\n]\n\n"
        + tail
    )


def dump_static_role() -> list[dict[str, object]]:
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".lean", prefix="v15-static-role-dump-", delete=False
    ) as stream:
        path = Path(stream.name)
        stream.write(static_dump_source())
    try:
        completed = run("lake", "env", "lean", str(path))
    finally:
        path.unlink(missing_ok=True)
    declarations = [json.loads(line) for line in completed.stdout.splitlines()]
    if len({item["name"] for item in declarations}) != len(declarations):
        raise ValueError("duplicate StaticRole declaration")
    return declarations


def axiom_class(axioms: list[str]) -> str:
    if not axioms:
        return "AXIOM-FREE"
    if axioms == ["propext"]:
        return "[propext]"
    if axioms == ["Quot.sound"]:
        return "[Quot.sound]"
    if axioms == ["Classical.choice"]:
        return "[Classical.choice]"
    return "MIXED/OTHER"


def counts_from_declarations(
    declarations: list[dict[str, object]], *, include_entries: bool
) -> dict[str, object]:
    by_kind: collections.Counter[str] = collections.Counter()
    by_module: collections.Counter[str] = collections.Counter()
    by_axiom: collections.Counter[str] = collections.Counter()
    entries: list[dict[str, object]] = []
    for item in declarations:
        kind = str(item["kind"])
        module = str(item["module"])
        axioms = [str(value) for value in item["axioms"]]
        by_kind[kind] += 1
        by_module[module] += 1
        by_axiom[axiom_class(axioms)] += 1
        if include_entries:
            value = item["value"]
            entries.append(
                {
                    "axioms": axioms,
                    "kind": kind,
                    "module": module,
                    "name": str(item["name"]),
                    "type_sha256": sha256(str(item["type"]).encode()),
                    "value_sha256": (
                        None if value is None else sha256(str(value).encode())
                    ),
                }
            )
    result: dict[str, object] = {
        "axiom_classes": dict(sorted(by_axiom.items())),
        "by_kind": dict(sorted(by_kind.items())),
        "by_module": dict(sorted(by_module.items())),
        "total": len(declarations),
    }
    if include_entries:
        result["declarations"] = sorted(entries, key=lambda item: str(item["name"]))
    return result


def historical_surface(path: Path) -> tuple[dict[str, object], str]:
    raw = path.read_bytes()
    document = json.loads(raw)
    return document, sha256(raw)


def combined_document() -> dict[str, object]:
    continuity, continuity_sha = historical_surface(CONTINUITY_MANIFEST)
    pj, pj_sha = historical_surface(PJ_MANIFEST)
    static_declarations = dump_static_role()
    static = counts_from_declarations(static_declarations, include_entries=True)

    surfaces = {
        "Continuity.Admission": {
            **continuity["counts"],
            "historical_manifest_sha256": continuity_sha,
            "historical_namespace": "Someone / SomeoneContinuityQualification",
            "public_namespace": "Continuity.Admission",
        },
        "PJ": {
            **pj["counts"],
            "historical_manifest_sha256": pj_sha,
            "namespace_normalization": (
                "SomeoneContinuity to ContinuityAdmission only"
            ),
        },
        "StaticRole": static,
    }

    totals = collections.Counter()
    theorem_total = 0
    declaration_total = 0
    for surface in surfaces.values():
        declaration_total += int(surface["total"])
        theorem_total += int(surface["by_kind"].get("theorem", 0))
        for name, count in surface["axiom_classes"].items() if "axiom_classes" in surface else surface["by_axiom_footprint"].items():
            totals[name] += int(count)

    hostile_static = sum(
        count
        for module, count in static["by_module"].items()
        if ".Countermodels." in module
    )
    hostile_continuity = int(
        continuity["counts"]["by_module"]["ContinuityQualification.Hostile"]
    )
    hostile_pj_modules = {
        "PJ.Hostile",
        "PJ.TrancheBPrime.AntiMinting",
        "PJ.TrancheCPrime.Ownership",
        "PJ.TrancheCPrime.ContextTransport",
        "PJ.TrancheDPrime.CollapseHostiles",
        "PJ.TrancheDPrime.OutOfSampleAdmissibility",
    }
    hostile_pj = sum(
        int(count)
        for module, count in pj["counts"]["by_module"].items()
        if module in hostile_pj_modules
    )

    return {
        "axiom_classes": {
            "AXIOM-FREE": totals["AXIOM-FREE"],
            "[propext]": totals["[propext]"],
            "[Quot.sound]": totals["[Quot.sound]"],
            "[Classical.choice]": totals["[Classical.choice]"],
            "MIXED/OTHER": totals["MIXED/OTHER"],
        },
        "declaration_total": declaration_total,
        "hostile_fixture_policy": (
            "compiled declarations in Continuity qualification hostile, "
            "StaticRole Countermodels, and exact PJ hostile/boundary modules"
        ),
        "hostile_module_declarations": {
            "Continuity.Admission": hostile_continuity,
            "PJ": hostile_pj,
            "StaticRole": hostile_static,
            "total": hostile_continuity + hostile_pj + hostile_static,
        },
        "integration_commit": INTEGRATION,
        "representative_collapse_count": len(REPRESENTATIVE_COLLAPSES),
        "representative_collapses": list(REPRESENTATIVE_COLLAPSES),
        "schema": "v15-public-declaration-footprint-v1",
        "scope": (
            "V15-owned Continuity Admission, StaticRole, and PJ modules; "
            "existing GT, Execution Custody, and Admissibility declarations "
            "remain governed by their separately pinned public receipts"
        ),
        "surfaces": surfaces,
        "theorem_total": theorem_total,
        "track_a_frozen_theorems": {
            "Inquiry": 74,
            "Preparation": 28,
            "axiom_free": 83,
            "propext": 19,
            "total": 102,
        },
    }


def render(document: dict[str, object]) -> bytes:
    return (json.dumps(document, indent=2, sort_keys=True) + "\n").encode()


def verify_claims() -> None:
    current = "\n".join(
        (ROOT / path).read_text()
        for path in (
            "README.md",
            "CHANGELOG.md",
            "CITATION.cff",
            "docs/V15-PUBLIC-INDEX.md",
            "docs/V15-RELEASE-CANDIDATE.md",
        )
    )
    required = (
        "ATLAS",
        "FRONTIER-NOT-COMPOSITIONAL",
        "NO-USEFUL-OWNERSHIP-COMMONALITY",
        "CONTEXT-TRANSPORT-NOT-GENERIC",
        "ONLY-DOMAIN-SPECIFIC-RESIDUAL-THEORIES",
    )
    if any(item not in current for item in required):
        raise ValueError("public Atlas or negative classification is absent")
    forbidden = (
        r"V15 (?:is|establishes|provides) (?:a )?universal calculus",
        r"V15 (?:is|establishes|provides) (?:a )?shared bridge algebra",
        r"V15 (?:implements|is) JCP",
        r"V15 (?:realizes|implements) (?:AG|NQ)",
        r"V15 (?:is|establishes) (?:Planet|Archipelago)",
    )
    if any(re.search(pattern, current, re.IGNORECASE) for pattern in forbidden):
        raise ValueError("affirmative public overclaim detected")


def verify_changed_paths() -> None:
    rows = PATH_MANIFEST.read_text().splitlines()
    if not rows or rows[0] != "gate\tpath":
        raise ValueError("V15 candidate path manifest header drift")
    listed = {row.split("\t", 1)[1] for row in rows[1:]}
    if any("\t" not in row for row in rows[1:]):
        raise ValueError("malformed V15 candidate path manifest row")
    committed = {
        line.decode()
        for line in run(
            "git", "diff", "--name-only", f"{INTEGRATION}..HEAD"
        ).stdout.splitlines()
    }
    status = run("git", "status", "--porcelain=v1").stdout.decode().splitlines()
    working = {line[3:] for line in status if len(line) >= 4}
    changed = committed | working
    unexpected = (
        changed
        - listed
        - POST_CANDIDATE_PRESENTATION_PATHS
        - POST_CANDIDATE_PROCESS_PATHS
    )
    if unexpected:
        raise ValueError(
            "path outside V15 candidate allowlist: " + ", ".join(sorted(unexpected))
        )
    absent = listed - changed
    permitted_absent = {
        "docs/V15-CANDIDATE-VERIFICATION-RECEIPT_2026-07-22.md"
    }
    if absent - permitted_absent:
        raise ValueError(
            "listed V15 candidate path is absent: "
            + ", ".join(sorted(absent - permitted_absent))
        )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    try:
        run("python3", "scripts/check-v15-integration.py")
        verify_claims()
        verify_changed_paths()
        expected = render(combined_document())
        if args.write:
            FOOTPRINT.write_bytes(expected)
        elif not FOOTPRINT.is_file():
            raise ValueError("V15 declaration footprint manifest is missing")
        elif FOOTPRINT.read_bytes() != expected:
            raise ValueError("V15 declaration footprint manifest drift")
        if 'version = "15.0.0"' not in (ROOT / "lakefile.toml").read_text():
            raise ValueError("Lake candidate version drift")
        citation = (ROOT / "CITATION.cff").read_text()
        if 'title: "V15 — Cross-Calculus Atlas"' not in citation:
            raise ValueError("citation title drift")
        if 'version: "15.0.0"' not in citation:
            raise ValueError("citation version drift")
        # Release causality: the tree is positioned as released BEFORE the tag
        # and GitHub release are built around it, because the release creation
        # is what mints the Zenodo version DOI. The operator chooses the
        # release date, so the tree asserts it; only the version DOI is
        # service-emitted and must never be guessed. An earlier revision of
        # this gate inverted that and rejected date-released outright
        # ("unreleased v15 metadata asserts a release date") — see AGENTS.md
        # "Release causality: the tree leads, the mint follows".
        if 'date-released: "2026-07-22"' not in citation:
            raise ValueError("citation date-released drift")
        if re.search(r"10\.5281/zenodo\.(?!20369489\b)\d+", citation):
            raise ValueError(
                "citation asserts a version DOI; only the concept DOI belongs here"
            )
    except (OSError, ValueError, subprocess.CalledProcessError, json.JSONDecodeError) as error:
        print(f"FAIL: V15 public qualification: {error}", file=sys.stderr)
        return 1
    document = json.loads(expected)
    print(
        "PASS — V15 public qualification footprint: "
        f"{document['declaration_total']} declarations, "
        f"{document['theorem_total']} theorems, "
        f"{document['hostile_module_declarations']['total']} hostile-module "
        "declarations, 12 representative collapses"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
