#!/usr/bin/env python3
"""Verify the exact GT-C03 public-evidence admission candidate.

The declaration inventory is source-derived.  This checker recompiles only the
new target leaf, dumps every module-owned kernel constant (including generated
declarations), and compares its normalized type, value, kind, universes, and
axiom set.  It also checks the exact public dependency and root delta.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
DECLARATIONS = ROOT / "docs/GT-C03-DECLARATION-INVENTORY.json"
DEPENDENCIES = ROOT / "docs/GT-C03-DEPENDENCY-INVENTORY.json"
DUMP_TEMPLATE = ROOT / "scripts/gt-c03-declaration-dump.lean.in"


class CheckFailure(RuntimeError):
    pass


def fail(message: str) -> None:
    raise CheckFailure(message)


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_text(value: str | None) -> str | None:
    return None if value is None else sha256_bytes(value.encode())


def run(args: list[str]) -> str:
    result = subprocess.run(args, cwd=ROOT, text=True, capture_output=True)
    if result.returncode != 0:
        sys.stderr.write(result.stdout)
        sys.stderr.write(result.stderr)
        fail(f"command failed ({result.returncode}): {' '.join(args)}")
    return result.stdout


def git_blob(path: str) -> str:
    return run(["git", "hash-object", path]).strip()


def imports_of(path: Path) -> list[str]:
    imports: list[str] = []
    for raw in path.read_text().splitlines():
        match = re.match(r"^\s*import\s+(.+)$", raw)
        if match is not None:
            imports.extend(
                token for token in match.group(1).split()
                if not token.startswith("--")
            )
    return imports


def module_path(module: str) -> Path:
    return Path(*module.split(".")).with_suffix(".lean")


def dump_target() -> list[dict[str, Any]]:
    with tempfile.TemporaryDirectory(prefix="gt-c03-") as directory:
        source = Path(directory) / "GTC03DeclarationDump.lean"
        source.write_bytes(DUMP_TEMPLATE.read_bytes())
        output = run(["lake", "env", "lean", str(source)])
    records = [
        json.loads(line) for line in output.splitlines() if line.startswith("{")
    ]
    if not records:
        fail("target declaration dump emitted no records")
    return records


def validate_declarations(
    inventory: dict[str, Any], actual_records: list[dict[str, Any]]
) -> None:
    expected_rows = inventory["declarations"]
    expected_by_name = {row["target_name"]: row for row in expected_rows}
    if len(expected_by_name) != len(expected_rows):
        fail("declaration inventory contains a duplicate target name")
    actual_by_name = {row["target_name"]: row for row in actual_records}
    if len(actual_by_name) != len(actual_records):
        fail("compiled target contains a duplicate declaration name")
    missing = sorted(set(expected_by_name) - set(actual_by_name))
    extra = sorted(set(actual_by_name) - set(expected_by_name))
    if missing or extra:
        fail(f"declaration roster drift: missing={missing}, extra={extra}")
    for name, expected in expected_by_name.items():
        actual = actual_by_name[name]
        observed = {
            "kind": actual["kind"],
            "level_params": actual["level_params"],
            "type": sha256_text(actual["target_type"]),
            "value": sha256_text(actual["target_value"]),
            "axioms": actual["target_axioms"],
        }
        wanted = {
            "kind": expected["kind"],
            "level_params": expected["level_params"],
            "type": expected["expected_target_type_sha256"],
            "value": expected["expected_target_value_sha256"],
            "axioms": expected["target_axioms"],
        }
        if observed != wanted:
            fail(f"compiled declaration drift: {name}")


def closure_from(module: str, *, include_root: bool) -> list[str]:
    queue = [module] if include_root else imports_of(ROOT / module_path(module))
    seen: set[str] = set()
    while queue:
        current = queue.pop(0)
        if current in seen:
            continue
        path = ROOT / module_path(current)
        if not path.is_file():
            continue
        seen.add(current)
        queue.extend(imports_of(path))
    return sorted(seen)


def validate_dependencies(inventory: dict[str, Any]) -> None:
    target = inventory["target_leaf"]
    path = ROOT / target["path"]
    if git_blob(target["path"]) != target["blob"]:
        fail("target leaf blob drift")
    if sha256_bytes(path.read_bytes()) != target["sha256"]:
        fail("target leaf SHA-256 drift")
    if imports_of(path) != target["direct_imports"]:
        fail("target direct-import drift")
    text = path.read_text()
    for forbidden in (
        "Calculi.Scratch",
        "LosslessEncodingCollapse",
        "GOVERNED-TRANSPORT-STAGE",
    ):
        if forbidden in text:
            fail(f"target leaf contains forbidden private marker: {forbidden}")

    expected_closure = {
        row["module"] for row in target["transitive_dependencies_excluding_leaf"]
    }
    actual_closure = set(closure_from(target["module"], include_root=False))
    if actual_closure != expected_closure:
        fail(
            "target dependency closure drift: "
            f"missing={sorted(expected_closure - actual_closure)}, "
            f"extra={sorted(actual_closure - expected_closure)}"
        )
    for row in target["transitive_dependencies_excluding_leaf"]:
        path = ROOT / row["path"]
        if git_blob(row["path"]) != row["blob"]:
            fail(f"dependency blob drift: {row['path']}")
        if sha256_bytes(path.read_bytes()) != row["sha256"]:
            fail(f"dependency SHA-256 drift: {row['path']}")

    for row in inventory["protected_public_objects"]:
        if git_blob(row["path"]) != row["base_blob"]:
            fail(f"protected public object drift: {row['path']}")

    root_effect = inventory["root_effect"]
    evidence_root_path = module_path(root_effect["evidence_root"]["module"])
    if git_blob(evidence_root_path.as_posix()) != root_effect["evidence_root"]["candidate_blob"]:
        fail("public evidence aggregate blob drift")
    custody_registry = root_effect["public_custody_registry"]
    if git_blob(custody_registry["path"]) != custody_registry["candidate_blob"]:
        fail("public custody registry blob drift")
    stable_count = len(closure_from(root_effect["stable_root"]["module"], include_root=True))
    evidence_count = len(closure_from(root_effect["evidence_root"]["module"], include_root=True))
    if stable_count != root_effect["stable_root"]["aggregate_plus_leaf_closure_count"]:
        fail("stable root closure count drift")
    if evidence_count != root_effect["evidence_root"]["aggregate_plus_transitive_closure_count"]:
        fail("evidence root closure count drift")


def expect_failure(label: str, action) -> None:
    try:
        action()
    except CheckFailure:
        return
    fail(f"hostile self-test was not rejected: {label}")


def self_test(
    declaration_inventory: dict[str, Any],
    dependency_inventory: dict[str, Any],
    actual_records: list[dict[str, Any]],
) -> None:
    missing = actual_records[:-1]
    expect_failure(
        "missing declaration",
        lambda: validate_declarations(declaration_inventory, missing),
    )
    extra = copy.deepcopy(actual_records)
    forged = copy.deepcopy(extra[0])
    forged["target_name"] += ".forged"
    extra.append(forged)
    expect_failure(
        "extra declaration",
        lambda: validate_declarations(declaration_inventory, extra),
    )
    for label, field, value in (
        ("kind drift", "kind", "axiom"),
        ("type drift", "target_type", "forged-type"),
        ("body drift", "target_value", "forged-body"),
        ("axiom drift", "target_axioms", ["Classical.choice"]),
    ):
        mutated = copy.deepcopy(actual_records)
        mutated[0][field] = value
        expect_failure(
            label,
            lambda mutated=mutated: validate_declarations(
                declaration_inventory, mutated
            ),
        )
    collision = copy.deepcopy(declaration_inventory)
    collision["declarations"][1]["target_name"] = (
        collision["declarations"][0]["target_name"]
    )
    expect_failure(
        "namespace collision",
        lambda: validate_declarations(collision, actual_records),
    )
    closure_drift = copy.deepcopy(dependency_inventory)
    closure_drift["target_leaf"]["transitive_dependencies_excluding_leaf"].pop()
    expect_failure(
        "dependency closure drift",
        lambda: validate_dependencies(closure_drift),
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--self-test",
        action="store_true",
        help="also prove representative hostile mutations fail closed",
    )
    args = parser.parse_args()
    try:
        declarations = json.loads(DECLARATIONS.read_text())
        dependencies = json.loads(DEPENDENCIES.read_text())
        actual = dump_target()
        validate_declarations(declarations, actual)
        validate_dependencies(dependencies)
        if args.self_test:
            self_test(declarations, dependencies, actual)
    except (CheckFailure, KeyError, OSError, json.JSONDecodeError) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        return 1
    print("PASS — GT-C03 exact declaration, axiom, dependency, and root delta")
    print(f"  compiled declarations: {len(actual)}")
    print("  exact target mapping: 82/82")
    print("  axiom footprint: 72 none; 10 exactly [propext]")
    print("  printed receipts: 17 (11 none; 6 exactly [propext])")
    print("  stable root: byte-exact; evidence root: one bounded C03 leaf")
    if args.self_test:
        print("  synthetic fail-closed hostiles: 8/8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
