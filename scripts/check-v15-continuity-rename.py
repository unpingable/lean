#!/usr/bin/env python3
"""Verify and record the exact Someone -> Continuity.Admission rename."""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
OLD_MANIFEST = (
    ROOT
    / "formalization/docs/someone-continuity-qualification-2026-07-22"
    / "declaration-manifest.json"
)
CORRESPONDENCE = ROOT / "docs/V15-CONTINUITY-ADMISSION-CORRESPONDENCE.tsv"
DUMP = ROOT / "formalization/scripts/ContinuityAdmissionDeclarationDump.lean"
CANDIDATE = "d1e2d18ffc6e27365ec890a6ae2439c87688b350"

NAME_MAP = (
    ("SomeoneContinuityQualification", "Continuity.Admission.Qualification"),
    ("Someone", "Continuity.Admission"),
)
MODULE_MAP = {
    "Someone": "Continuity.Admission",
    "ContinuityQualification.Core": "Continuity.Admission.Qualification.Core",
    "ContinuityQualification.Hostile": (
        "Continuity.Admission.Qualification.Hostile"
    ),
}
PATH_MAP = {
    "someone/Someone.lean": "formalization/Continuity/Admission.lean",
    "formalization/ContinuityQualification/Core.lean": (
        "formalization/Continuity/Admission/Qualification/Core.lean"
    ),
    "formalization/ContinuityQualification/Hostile.lean": (
        "formalization/Continuity/Admission/Qualification/Hostile.lean"
    ),
}
FIELDS = (
    "private_name",
    "public_name",
    "kind",
    "private_source_path",
    "public_source_path",
    "private_type_sha256",
    "public_type_sha256",
    "namespace_normalized_type_sha256",
    "type_identity_after_namespace_normalization",
    "axiom_footprint",
    "private_value_sha256",
    "public_value_sha256",
    "namespace_normalized_value_sha256",
    "proof_body_changed_beyond_namespace_elaboration",
)


def sha256(value: str) -> str:
    return hashlib.sha256(value.encode()).hexdigest()


def rename(value: str) -> str:
    if value.startswith("_private.Someone.0.Someone."):
        return value.replace(
            "_private.Someone.0.Someone.",
            "_private.Continuity.Admission.0.Continuity.Admission.",
            1,
        )
    for old, new in NAME_MAP:
        if value == old or value.startswith(old + "."):
            return new + value[len(old) :]
    raise ValueError(f"unmapped private declaration: {value}")


def unrename_expression(value: str) -> str:
    result = compact_expression(value)
    for old, new in NAME_MAP:
        result = result.replace(new, old)
    # Lean's elaborator quotes the generated name used inside the proof of
    # `blocked.eq_2` as a nested `Lean.Name.mkStr` expression.  The source
    # file identity seed remains `_private.Someone`; only the namespace path
    # gains the two public components.  Normalize that structural spelling
    # exactly, rather than treating it as a proof-body change.
    result = result.replace(
        '(Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum '
        '`_private.Someone 0) "Continuity") "Admission")',
        '(Lean.Name.mkStr (Lean.Name.mkNum `_private.Someone 0) "Someone")',
    )
    return result


def compact_expression(value: str) -> str:
    return re.sub(r"\s+", " ", value).strip()


def dump_public() -> list[dict[str, object]]:
    completed = subprocess.run(
        [
            "lake",
            "env",
            "lean",
            str(DUMP.relative_to(ROOT)),
        ],
        cwd=ROOT,
        check=True,
        text=True,
        stdout=subprocess.PIPE,
    )
    return [json.loads(line) for line in completed.stdout.splitlines()]


def dump_private() -> list[dict[str, object]]:
    paths = (
        "someone/Someone.lean",
        "formalization/ContinuityQualification/Core.lean",
        "formalization/ContinuityQualification/Hostile.lean",
        "formalization/scripts/SomeoneContinuityDeclarationDump.lean",
    )
    base_lean_path = subprocess.run(
        ["lake", "env", "printenv", "LEAN_PATH"],
        cwd=ROOT,
        check=True,
        text=True,
        stdout=subprocess.PIPE,
    ).stdout.strip()
    lean = subprocess.run(
        ["lake", "env", "which", "lean"],
        cwd=ROOT,
        check=True,
        text=True,
        stdout=subprocess.PIPE,
    ).stdout.strip()
    with tempfile.TemporaryDirectory(prefix="v15-continuity-private-") as raw:
        temp = Path(raw)
        for path in paths:
            destination = temp / path
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_bytes(candidate_bytes(path))
        lib = temp / "lib"
        (lib / "ContinuityQualification").mkdir(parents=True)
        env = os.environ.copy()
        env["LEAN_PATH"] = f"{lib}:{base_lean_path}"

        compile_jobs = (
            (
                temp / "someone",
                temp / "someone/Someone.lean",
                lib / "Someone.olean",
            ),
            (
                temp / "formalization",
                temp / "formalization/ContinuityQualification/Core.lean",
                lib / "ContinuityQualification/Core.olean",
            ),
            (
                temp / "formalization",
                temp / "formalization/ContinuityQualification/Hostile.lean",
                lib / "ContinuityQualification/Hostile.olean",
            ),
        )
        for root, source, output in compile_jobs:
            subprocess.run(
                [lean, "-R", str(root), "-o", str(output), str(source)],
                cwd=ROOT,
                env=env,
                check=True,
                stdout=subprocess.PIPE,
            )
        completed = subprocess.run(
            [
                lean,
                "-R",
                str(temp / "formalization"),
                str(
                    temp
                    / "formalization/scripts/SomeoneContinuityDeclarationDump.lean"
                ),
            ],
            cwd=ROOT,
            env=env,
            check=True,
            text=True,
            stdout=subprocess.PIPE,
        )
    return [json.loads(line) for line in completed.stdout.splitlines()]


def candidate_bytes(path: str) -> bytes:
    return subprocess.run(
        ["git", "-C", str(ROOT), "show", f"{CANDIDATE}:{path}"],
        check=True,
        stdout=subprocess.PIPE,
    ).stdout


def verify_primary_source_rewrite() -> None:
    old = candidate_bytes("someone/Someone.lean")
    expected = old.replace(
        b"namespace Someone\n", b"namespace Continuity.Admission\n"
    ).replace(b"end Someone\n", b"end Continuity.Admission\n")
    actual = (ROOT / "formalization/Continuity/Admission.lean").read_bytes()
    if actual != expected:
        raise ValueError("primary source differs beyond the exact namespace rename")
    if (ROOT / "someone/Someone.lean").exists():
        raise ValueError("duplicate authoritative Someone implementation remains")


def expected_rows() -> list[dict[str, str]]:
    old_document = json.loads(OLD_MANIFEST.read_text())
    old_declarations = old_document["declarations"]
    private_declarations = dump_private()
    public_declarations = dump_public()
    private_by_name = {item["name"]: item for item in private_declarations}
    public_by_name = {item["name"]: item for item in public_declarations}
    if len(private_by_name) != len(private_declarations):
        raise ValueError("duplicate declaration in private dump")
    if len(public_by_name) != len(public_declarations):
        raise ValueError("duplicate declaration in public dump")
    if (
        len(old_declarations) != 1005
        or len(private_declarations) != 1005
        or len(public_declarations) != 1005
    ):
        raise ValueError("declaration count changed from the ratified 1,005")

    rows: list[dict[str, str]] = []
    for old in old_declarations:
        public_name = rename(old["name"])
        private = private_by_name.pop(old["name"], None)
        public = public_by_name.pop(public_name, None)
        if private is None:
            raise ValueError(f"missing private declaration: {old['name']}")
        if public is None:
            raise ValueError(f"missing renamed declaration: {public_name}")
        if public["module"] != MODULE_MAP[old["source_module"]]:
            raise ValueError(f"module attribution changed: {public_name}")
        if public["kind"] != old["kind"]:
            raise ValueError(f"declaration kind changed: {public_name}")

        if sha256(private["type"]) != old["normalized_type_sha256"]:
            raise ValueError(f"private manifest type drift: {old['name']}")
        normalized_type = compact_expression(
            unrename_expression(public["type"])
        )
        private_normalized_type = compact_expression(private["type"])
        normalized_type_sha = sha256(normalized_type)
        if normalized_type != private_normalized_type:
            raise ValueError(f"statement/type changed: {public_name}")

        public_axioms = [unrename_expression(item) for item in public["axioms"]]
        if public_axioms != old["normalized_axioms"]:
            raise ValueError(f"axiom footprint changed: {public_name}")

        old_value_sha = old["normalized_value_sha256"]
        private_value = private["value"]
        public_value = public["value"]
        if public_value is None:
            public_value_sha = "-"
            normalized_value_sha = "-"
            if old_value_sha is not None:
                raise ValueError(f"proof/value disappeared: {public_name}")
        else:
            if private_value is None or sha256(private_value) != old_value_sha:
                raise ValueError(f"private manifest value drift: {old['name']}")
            public_value_sha = sha256(public_value)
            normalized_public_value = compact_expression(
                unrename_expression(public_value)
            )
            normalized_private_value = compact_expression(private_value)
            normalized_value_sha = sha256(normalized_public_value)
            if normalized_public_value != normalized_private_value:
                raise ValueError(f"proof/value changed: {public_name}")

        rows.append(
            {
                "private_name": old["name"],
                "public_name": public_name,
                "kind": old["kind"],
                "private_source_path": old["source_path"],
                "public_source_path": PATH_MAP[old["source_path"]],
                "private_type_sha256": old["normalized_type_sha256"],
                "public_type_sha256": sha256(public["type"]),
                "namespace_normalized_type_sha256": normalized_type_sha,
                "type_identity_after_namespace_normalization": "true",
                "axiom_footprint": old["normalized_axiom_receipt"],
                "private_value_sha256": old_value_sha or "-",
                "public_value_sha256": public_value_sha,
                "namespace_normalized_value_sha256": normalized_value_sha,
                "proof_body_changed_beyond_namespace_elaboration": "false",
            }
        )
    if private_by_name:
        raise ValueError(
            "unexpected private declarations: "
            + ", ".join(sorted(private_by_name))
        )
    if public_by_name:
        raise ValueError(
            "unexpected public declarations: " + ", ".join(sorted(public_by_name))
        )
    return rows


def render(rows: list[dict[str, str]]) -> str:
    lines = ["\t".join(FIELDS)]
    lines.extend("\t".join(row[field] for field in FIELDS) for row in rows)
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    try:
        verify_primary_source_rewrite()
        expected = render(expected_rows())
        if args.write:
            CORRESPONDENCE.write_text(expected)
        elif not CORRESPONDENCE.is_file():
            raise ValueError("correspondence manifest is missing")
        elif CORRESPONDENCE.read_text() != expected:
            raise ValueError("correspondence manifest drift")
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        print(f"FAIL: Continuity rename exactness: {error}", file=sys.stderr)
        return 1
    print(
        "PASS — 1,005 declarations preserve type, value, and axiom identity "
        "under the exact Continuity.Admission namespace rename"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
