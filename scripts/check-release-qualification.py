#!/usr/bin/env python3
"""Live release-qualification gate.

Version-agnostic successor to ``check-v15-public-qualification.py``. That
checker was a campaign gate: it pinned release metadata to V15 literals and
diffed every changed path against a frozen allowlist rooted at one commit.
Both are correct for qualifying one candidate and wrong for a checker that
runs at every future HEAD — a later release makes them false by construction,
so the gate blocks the tree instead of checking it.

What survives here is what stays true across releases:

* release metadata is internally *consistent* (lakefile <-> CITATION.cff <->
  CHANGELOG), rather than equal to one release's literals;
* ``CITATION.cff`` carries the concept DOI and never a version DOI;
* registered claim-preservation invariants hold (data-driven, see
  ``scripts/release-invariants.tsv``);
* the V15 declaration-footprint census still reproduces exactly.

A new release never needs this file edited. It does need two TSV rows: the
claims it must keep stated (``release-invariants.tsv``, enforced — a new major
version with no row is an error) and any new public Lean source it admits past
the transfer freeze (``post-transfer-admissions.tsv``, read by
``check-v15-integration.py``). If a surface legitimately changes, regenerate
the census with ``--write`` and commit the diff. Those are the checkpoints;
none of them is a code change.

The frozen campaign gate stays at ``check-v15-public-qualification.py`` and is
run in a detached worktree at ``v15.0.0``; see AGENTS.md.
"""

from __future__ import annotations

import argparse
import collections
import datetime
import hashlib
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
# The census below is a frozen accounting of the V15-owned surfaces. The commit
# identifies that accounting's baseline and is embedded in the manifest; it is
# not a pin on the current tree.
INTEGRATION = "1f0e0208584e0f61fe49353dd0fc6b4775e22e00"
FOOTPRINT = ROOT / "docs/V15-PUBLIC-DECLARATION-FOOTPRINT.json"
INVARIANTS = ROOT / "scripts/release-invariants.tsv"
CONTINUITY_MANIFEST = (
    ROOT
    / "formalization/docs/someone-continuity-qualification-2026-07-22"
    / "declaration-manifest.json"
)
PJ_MANIFEST = (
    ROOT / "formalization/PJ/Campaign/tranche-d-prime-declaration-manifest.json"
)
STATIC_TEMPLATE = ROOT / "formalization/scripts/PJTrancheDPrimeDeclarationDump.lean"

CONCEPT_DOI = "10.5281/zenodo.20369489"

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


# --------------------------------------------------------------------------
# Release metadata consistency
# --------------------------------------------------------------------------


def release_version() -> str:
    """The version the tree asserts, read from the tree rather than pinned."""
    text = (ROOT / "lakefile.toml").read_text()
    match = re.search(r'^version\s*=\s*"([^"]+)"', text, re.M)
    if not match:
        raise ValueError("lakefile.toml declares no version")
    version = match.group(1)
    # Accept SemVer prerelease/build metadata (v1.3.0-rc1 exists in this repo's
    # tag history); reject anything that is not a version.
    if not re.fullmatch(r"\d+\.\d+\.\d+(?:-[0-9A-Za-z.-]+)?(?:\+[0-9A-Za-z.-]+)?", version):
        raise ValueError(f"lakefile version is not semantic: {version!r}")
    return version


def verify_release_metadata() -> tuple[str, str]:
    """Metadata must agree with itself; no release literal is hardcoded here.

    Release causality (AGENTS.md): the operator chooses the version, title and
    date, so the tree asserts them before the tag exists. Only the Zenodo
    version DOI is service-emitted, and it must never appear here. An earlier
    revision of the predecessor gate inverted this and rejected `date-released`
    outright on an unreleased tree, which left the tag nothing coherent to
    archive. This gate therefore requires a release date to be present and
    consistent, and never requires it to be absent.
    """
    version = release_version()
    citation = (ROOT / "CITATION.cff").read_text()

    cited = re.search(r'^version:\s*"([^"]+)"', citation, re.M)
    if not cited:
        raise ValueError("CITATION.cff declares no version")
    if cited.group(1) != version:
        raise ValueError(
            f"version drift: lakefile.toml {version!r} vs "
            f"CITATION.cff {cited.group(1)!r}"
        )

    title = re.search(r'^title:\s*"([^"]+)"', citation, re.M)
    if not title or not title.group(1).strip():
        raise ValueError("CITATION.cff declares no title")

    released = re.search(r'^date-released:\s*"(\d{4}-\d{2}-\d{2})"', citation, re.M)
    if not released:
        raise ValueError(
            "CITATION.cff carries no well-formed date-released; the tree must be "
            "positioned as released before the tag is built around it"
        )
    date = released.group(1)
    try:
        datetime.date.fromisoformat(date)
    except ValueError:
        raise ValueError(f"date-released is not a real calendar date: {date}") from None

    # Field-aware, not prose-aware: the concept DOI appearing somewhere in the
    # file must not excuse a wrong `doi:` field, and a whole-DOI match must not
    # be satisfied by a longer identifier that merely starts with it.
    doi_field = re.search(r'^doi:\s*"([^"]*)"', citation, re.M)
    if not doi_field:
        raise ValueError("CITATION.cff declares no doi field")
    if doi_field.group(1) != CONCEPT_DOI:
        raise ValueError(
            f"doi field is {doi_field.group(1)!r}; it must be the concept DOI "
            f"{CONCEPT_DOI}, which identifies the series and never moves"
        )
    identifiers = re.findall(
        r'^\s*(?:-\s*)?value:\s*"(10\.5281/zenodo\.[^"]*)"', citation, re.M
    )
    mentioned = set(re.findall(r"10\.5281/zenodo\.[0-9A-Za-z./-]+", citation))
    stray = sorted((set(identifiers) | mentioned) - {CONCEPT_DOI})
    if stray:
        raise ValueError(
            f"CITATION.cff asserts {', '.join(stray)}; only the concept DOI "
            "belongs here — a version DOI is minted by Zenodo and recorded there"
        )

    changelog = (ROOT / "CHANGELOG.md").read_text()
    heading = re.search(
        r"^## " + re.escape(version) + r" — .+ \((\d{4}-\d{2}-\d{2})\)$",
        changelog,
        re.M,
    )
    if not heading:
        raise ValueError(f"CHANGELOG.md has no released entry for {version}")
    if heading.group(1) != date:
        raise ValueError(
            f"release date drift: CITATION.cff {date} vs CHANGELOG.md "
            f"{heading.group(1)} for {version}"
        )

    return version, date


# --------------------------------------------------------------------------
# Claim-preservation invariants (data-driven)
# --------------------------------------------------------------------------


def verify_claim_invariants(version: str) -> int:
    """Check registered claim invariants and that this release registered some.

    These are tripwires, not semantic proofs. `require` catches deletion of a
    stated classification and `forbid` catches a known overclaim phrasing;
    neither can detect prose that negates a token while keeping it present, or
    an overclaim worded around the pattern. Coverage is enforced so a release
    cannot ship having registered nothing, which is the failure the tripwires
    would otherwise hide.
    """
    rows = [
        line
        for line in INVARIANTS.read_text().splitlines()
        if line.strip() and not line.startswith("#")
    ]
    # Sibling registries (public-custody.tsv, stable-surfaces.tsv) carry a bare
    # column header, so tolerate one here rather than failing with a confusing
    # "unknown invariant kind 'release'".
    if rows and rows[0].split("\t")[0].strip() == "release":
        rows = rows[1:]
    if not rows:
        raise ValueError("release-invariants.tsv registers no invariants")
    cache: dict[str, str] = {}
    failures: list[str] = []
    releases: set[str] = set()
    for number, row in enumerate(rows, start=1):
        fields = row.split("\t")
        if len(fields) != 5:
            raise ValueError(f"malformed release-invariants.tsv row {number}")
        release, kind, pattern, scope, note = (field.strip() for field in fields)
        if not all((release, kind, pattern, scope)):
            raise ValueError(
                f"release-invariants.tsv row {number} has an empty field; an "
                "empty require pattern would match every tree"
            )
        if kind not in {"require", "forbid"}:
            raise ValueError(f"unknown invariant kind {kind!r} on row {number}")
        releases.add(release)
        if scope not in cache:
            chunks = []
            for relative in scope.split(","):
                path = ROOT / relative.strip()
                if not path.is_file():
                    raise ValueError(
                        f"release-invariants.tsv row {number} names a missing "
                        f"scope file: {relative.strip()}"
                    )
                chunks.append(path.read_text())
            cache[scope] = "\n".join(chunks)
        text = cache[scope]
        if kind == "require" and pattern not in text:
            failures.append(f"absent required claim {pattern!r} ({note})")
        elif kind == "forbid" and re.search(pattern, text, re.IGNORECASE):
            failures.append(f"overclaim matched {pattern!r} ({note})")
    if failures:
        raise ValueError("; ".join(failures))
    current = f"v{version.split('.')[0]}"
    if current not in releases:
        raise ValueError(
            f"release-invariants.tsv registers no {current} row — add the "
            f"claims {current} must keep stated and the overclaims it must not "
            "make. This is a one-line TSV edit, not a code change."
        )
    return len(rows)


# --------------------------------------------------------------------------
# V15 declaration-footprint census (unchanged accounting)
# --------------------------------------------------------------------------


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


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--write",
        action="store_true",
        help="regenerate the declaration-footprint manifest instead of comparing",
    )
    args = parser.parse_args()
    try:
        run("python3", "scripts/check-v15-integration.py")
        version, date = verify_release_metadata()
        invariants = verify_claim_invariants(version)
        expected = render(combined_document())
        if args.write:
            FOOTPRINT.write_bytes(expected)
        elif not FOOTPRINT.is_file():
            raise ValueError("declaration footprint manifest is missing")
        elif FOOTPRINT.read_bytes() != expected:
            raise ValueError(
                "declaration footprint manifest drift — if the surface changed "
                "on purpose, rerun with --write and commit the diff"
            )
    except (
        OSError,
        ValueError,
        subprocess.CalledProcessError,
        json.JSONDecodeError,
    ) as error:
        print(f"FAIL: release qualification: {error}", file=sys.stderr)
        return 1
    document = json.loads(expected)
    print(
        f"PASS — release qualification for {version} ({date}): "
        f"{invariants} claim invariants, "
        f"{document['declaration_total']} declarations, "
        f"{document['theorem_total']} theorems, "
        f"{document['hostile_module_declarations']['total']} hostile-module "
        f"declarations, {document['representative_collapse_count']} "
        "representative collapses"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
