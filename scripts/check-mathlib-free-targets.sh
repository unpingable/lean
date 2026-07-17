#!/usr/bin/env bash
# Fail-closed public Lake-project and import-policy gate.
#
# Every repository-owned lakefile.toml (dependencies excluded) and every one of
# its lean_libs must appear exactly once in public-targets.tsv. Direct roots are
# explicit, glob-free, and custody-correct. Current-tree targets are walked
# through their complete local import closure; stable targets remain exact with
# stable-surfaces.tsv and Mathlib-free targets may not reach Mathlib.
# Pinned-external fixtures instead prove that every direct dependency is an
# exact Git requirement whose committed Lake lock resolves to a commit SHA.

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
exec python3 - "$REPO_ROOT" <<'PY'
from __future__ import annotations

import json
import re
import sys
import tomllib
from collections import defaultdict, deque
from dataclasses import dataclass
from pathlib import Path, PurePosixPath


repo = Path(sys.argv[1]).resolve()
registry_path = repo / "scripts/public-targets.tsv"
custody_path = repo / "scripts/public-custody.tsv"
stable_path = repo / "scripts/stable-surfaces.tsv"

for required in (registry_path, custody_path, stable_path):
    if not required.is_file():
        print(f"FAIL: missing public target source of truth: {required.relative_to(repo)}", file=sys.stderr)
        raise SystemExit(1)

failures: list[str] = []


def fail(message: str) -> None:
    failures.append(message)


def rows(path: Path, width: int):
    for line_number, raw in enumerate(path.read_text().splitlines(), 1):
        if not raw or raw.startswith("#"):
            continue
        fields = raw.split("\t")
        if len(fields) != width or any(not field for field in fields):
            fail(
                f"malformed row in {path.relative_to(repo)}:{line_number} "
                f"(expected {width} nonempty tab-separated columns)"
            )
            continue
        yield line_number, fields


def safe_project(value: str) -> bool:
    if value == ".":
        return True
    path = PurePosixPath(value)
    return not path.is_absolute() and ".." not in path.parts and str(path) == value


def module_relpath(module: str, src_dir: str = ".") -> PurePosixPath:
    module_path = PurePosixPath(*module.split(".")).with_suffix(".lean")
    return module_path if src_dir == "." else PurePosixPath(src_dir) / module_path


def repo_rel(path: Path) -> str:
    return path.relative_to(repo).as_posix()


def imports_of(path: Path) -> list[str]:
    imports: list[str] = []
    for raw in path.read_text().splitlines():
        match = re.match(r"^\s*import\s+(.+)$", raw)
        if match is None:
            continue
        for token in match.group(1).split():
            if token.startswith("--"):
                break
            imports.append(token)
    return imports


@dataclass(frozen=True)
class Target:
    project: str
    name: str
    role: str
    import_policy: str
    build_policy: str


allowed_roles = {"stable-surface", "public-evidence", "repository-aggregate"}
allowed_import_policies = {
    "mathlib-free",
    "mathlib-island",
    "mathlib-reaching",
    "pinned-external",
}
allowed_build_policies = {"default", "explicit"}

targets: dict[tuple[str, str], Target] = {}
for line_number, fields in rows(registry_path, 5):
    project, name, role, import_policy, build_policy = fields
    key = (project, name)
    if not safe_project(project):
        fail(f"unsafe/noncanonical project path in public-targets.tsv:{line_number}: {project}")
    if key in targets:
        fail(f"duplicate target in public-targets.tsv:{line_number}: {project}/{name}")
        continue
    if role not in allowed_roles:
        fail(f"unrecognized target role: {project}/{name} -> {role}")
    if import_policy not in allowed_import_policies:
        fail(f"unrecognized import policy: {project}/{name} -> {import_policy}")
    if build_policy not in allowed_build_policies:
        fail(f"unrecognized build policy: {project}/{name} -> {build_policy}")
    if import_policy in {"mathlib-island", "mathlib-reaching"} and build_policy != "explicit":
        fail(f"Mathlib-reaching target must be explicit-only: {project}/{name}")
    if role == "stable-surface" and project != ".":
        fail(f"registered stable target must belong to the root project: {project}/{name}")
    targets[key] = Target(project, name, role, import_policy, build_policy)


source_role: dict[str, str] = {}
for line_number, fields in rows(custody_path, 3):
    path, role, _owners = fields
    if path in source_role:
        fail(f"duplicate path in public-custody.tsv:{line_number}: {path}")
    source_role[path] = role


stable_roots: dict[str, set[str]] = defaultdict(set)
stable_policies: dict[str, set[str]] = defaultdict(set)
for line_number, fields in rows(stable_path, 4):
    _surface, target_name, root_module, import_policy = fields
    if root_module in stable_roots[target_name]:
        fail(f"duplicate stable target/root in stable-surfaces.tsv:{line_number}: {target_name}/{root_module}")
    stable_roots[target_name].add(root_module)
    stable_policies[target_name].add(import_policy)


excluded_dirs = {".git", ".lake", "lake-packages"}
lakefiles: dict[str, Path] = {}
for candidate in repo.rglob("lakefile.toml"):
    relative = candidate.relative_to(repo)
    if any(part in excluded_dirs for part in relative.parts[:-1]):
        continue
    project = relative.parent.as_posix()
    project = "." if project == "." else project
    lakefiles[project] = candidate

registered_projects = {target.project for target in targets.values()}
actual_projects = set(lakefiles)
for project in sorted(actual_projects - registered_projects):
    fail(f"unregistered Lake project: {project}/lakefile.toml")
for project in sorted(registered_projects - actual_projects):
    fail(f"registered Lake project has no lakefile.toml: {project}")


def validate_external_pins(project: str, data: dict) -> None:
    project_dir = repo if project == "." else repo / project
    manifest_path = project_dir / "lake-manifest.json"
    toolchain_path = project_dir / "lean-toolchain"
    if not toolchain_path.is_file():
        fail(f"pinned-external project has no Lean toolchain pin: {repo_rel(toolchain_path)}")
    else:
        toolchain = toolchain_path.read_text().strip()
        if re.fullmatch(r"leanprover/lean4:v[0-9]+\.[0-9]+\.[0-9]+", toolchain) is None:
            fail(f"pinned-external project has a non-release toolchain ref: {project}/{toolchain!r}")
    requirements = data.get("require", [])
    if not isinstance(requirements, list) or not requirements:
        fail(f"pinned-external project has no direct requirements: {project}")
        return

    declared: dict[str, tuple[str, str]] = {}
    for requirement in requirements:
        if not isinstance(requirement, dict):
            fail(f"malformed requirement in pinned-external project: {project}")
            continue
        name = requirement.get("name")
        git = requirement.get("git")
        revision = requirement.get("rev")
        if not all(isinstance(value, str) and value for value in (name, git, revision)):
            fail(
                f"pinned-external requirement needs explicit name/git/rev: "
                f"{project}/{name or '<unnamed>'}"
            )
            continue
        if (
            re.fullmatch(r"[0-9a-fA-F]{40}", revision) is None
            and re.fullmatch(r"v[0-9]+\.[0-9]+\.[0-9]+", revision) is None
        ):
            fail(f"pinned-external requirement uses a moving/non-release ref: {project}/{name}@{revision}")
        if name in declared:
            fail(f"duplicate direct requirement in {project}/lakefile.toml: {name}")
        declared[name] = (git, revision)

    if not manifest_path.is_file():
        fail(f"pinned-external project has no committed Lake manifest: {repo_rel(manifest_path)}")
        return
    try:
        manifest = json.loads(manifest_path.read_text())
    except (OSError, json.JSONDecodeError) as error:
        fail(f"cannot read pinned-external manifest {repo_rel(manifest_path)}: {error}")
        return

    if manifest.get("name") != data.get("name"):
        fail(
            f"project/manifest name mismatch in {project}: "
            f"{data.get('name')!r} != {manifest.get('name')!r}"
        )
    direct_locked: dict[str, dict] = {}
    for package in manifest.get("packages", []):
        if isinstance(package, dict) and package.get("inherited") is False:
            name = package.get("name")
            if isinstance(name, str):
                direct_locked[name] = package

    if set(declared) != set(direct_locked):
        fail(
            f"direct requirement/manifest drift in {project}: "
            f"lakefile={sorted(declared)}, manifest={sorted(direct_locked)}"
        )
    for name, (git, revision) in declared.items():
        package = direct_locked.get(name)
        if package is None:
            continue
        if package.get("type") != "git" or package.get("url") != git:
            fail(f"locked source drift for {project} requirement {name}")
        if package.get("inputRev") != revision:
            fail(
                f"locked input revision drift for {project} requirement {name}: "
                f"{revision!r} != {package.get('inputRev')!r}"
            )
        resolved = package.get("rev")
        if not isinstance(resolved, str) or re.fullmatch(r"[0-9a-fA-F]{40}", resolved) is None:
            fail(f"requirement {project}/{name} is not locked to a commit SHA")


project_data: dict[str, dict] = {}
project_libs: dict[str, dict[str, dict]] = {}
for project, lakefile in sorted(lakefiles.items()):
    try:
        data = tomllib.loads(lakefile.read_text())
    except (OSError, tomllib.TOMLDecodeError) as error:
        fail(f"cannot parse {repo_rel(lakefile)}: {error}")
        continue
    project_data[project] = data

    raw_libs = data.get("lean_lib", [])
    if not isinstance(raw_libs, list):
        fail(f"lean_lib is not an array in {repo_rel(lakefile)}")
        raw_libs = []
    libs: dict[str, dict] = {}
    for lib in raw_libs:
        name = lib.get("name") if isinstance(lib, dict) else None
        if not isinstance(name, str) or not name:
            fail(f"unnamed/malformed lean_lib in {repo_rel(lakefile)}")
            continue
        if name in libs:
            fail(f"duplicate lean_lib in {repo_rel(lakefile)}: {name}")
        libs[name] = lib
    project_libs[project] = libs

    actual = set(libs)
    registered = {target.name for target in targets.values() if target.project == project}
    for name in sorted(actual - registered):
        fail(f"unregistered lean_lib target: {project}/{name}")
    for name in sorted(registered - actual):
        fail(f"registered target missing from {repo_rel(lakefile)}: {project}/{name}")

    defaults = data.get("defaultTargets", [])
    if not isinstance(defaults, list) or not all(isinstance(item, str) for item in defaults):
        fail(f"defaultTargets is not a string array in {repo_rel(lakefile)}")
        defaults = []
    if len(defaults) != len(set(defaults)):
        fail(f"duplicate entry in {repo_rel(lakefile)} defaultTargets")
    actual_defaults = set(defaults)
    registered_defaults = {
        target.name
        for target in targets.values()
        if target.project == project and target.build_policy == "default"
    }
    if actual_defaults != registered_defaults:
        fail(
            f"default target policy drift in {project}: "
            f"lakefile={sorted(actual_defaults)}, registry={sorted(registered_defaults)}"
        )

    if any(target.import_policy == "pinned-external" for target in targets.values() if target.project == project):
        validate_external_pins(project, data)


expected_root_roles = {
    "stable-surface": "STABLE-SURFACE",
    "public-evidence": "PUBLIC-EVIDENCE",
    "repository-aggregate": "REPOSITORY-AGGREGATE",
}

walked_targets = 0
mathlib_free_targets = 0
pinned_external_targets = 0
ownerships = 0
external_boundaries = 0

for key, target in sorted(targets.items()):
    data = project_data.get(target.project)
    lib = project_libs.get(target.project, {}).get(target.name)
    if data is None or lib is None:
        continue

    if "globs" in lib:
        fail(f"public target uses globs; exact roots are required: {target.project}/{target.name}")
    roots = lib.get("roots")
    if not isinstance(roots, list) or not roots or not all(isinstance(root, str) and root for root in roots):
        fail(f"public target needs nonempty explicit roots: {target.project}/{target.name}")
        continue
    if len(roots) != len(set(roots)):
        fail(f"duplicate root in public target: {target.project}/{target.name}")

    src_dir = lib.get("srcDir", ".")
    if not isinstance(src_dir, str) or not safe_project(src_dir):
        fail(f"unsafe/noncanonical srcDir for {target.project}/{target.name}: {src_dir!r}")
        continue
    project_dir = repo if target.project == "." else repo / target.project

    expected_role = expected_root_roles[target.role]
    for module in roots:
        path = project_dir / module_relpath(module, src_dir)
        role = source_role.get(repo_rel(path) if path.is_relative_to(repo) else "", "<unregistered>")
        if role != expected_role:
            fail(
                f"{target.project}/{target.name} ({expected_role}) directly roots "
                f"{repo_rel(path)} ({role})"
            )

    if target.role == "stable-surface":
        expected_roots = stable_roots.get(target.name, set())
        if set(roots) != expected_roots:
            fail(
                f"stable target roots drifted from stable-surfaces.tsv: {target.name}; "
                f"Lake={sorted(roots)}, registered={sorted(expected_roots)}"
            )
        policies = stable_policies.get(target.name, set())
        if policies != {target.import_policy}:
            fail(
                f"stable target policy drifted from stable-surfaces.tsv: {target.name}; "
                f"target={target.import_policy}, registered={sorted(policies)}"
            )

    local_prefixes = {root.split(".", 1)[0] for root in roots}
    seen: set[str] = set()
    queue = deque(roots)
    target_external_imports = 0
    while queue:
        module = queue.popleft()
        if module in seen:
            continue
        seen.add(module)
        path = project_dir / module_relpath(module, src_dir)
        if not path.is_file():
            fail(f"{target.project}/{target.name} reaches missing local source: {module} -> {repo_rel(path)}")
            continue

        path_role = source_role.get(repo_rel(path), "<unregistered>")
        if target.role == "stable-surface" and path_role != "STABLE-SURFACE":
            fail(f"stable target {target.name} reaches {repo_rel(path)} ({path_role})")
        elif target.role == "public-evidence" and path_role not in {"PUBLIC-EVIDENCE", "STABLE-SURFACE"}:
            fail(f"evidence target {target.project}/{target.name} reaches {repo_rel(path)} ({path_role})")
        elif target.role == "repository-aggregate" and path_role == "<unregistered>":
            fail(f"aggregate target {target.name} reaches unregistered source {repo_rel(path)}")

        for imported in imports_of(path):
            if imported == "Mathlib" or imported.startswith("Mathlib."):
                if target.import_policy == "mathlib-free":
                    fail(f"{target.project}/{target.name} is not Mathlib-free: {module} imports {imported}")
                continue
            if imported == "LeanProofs.Scratch" or imported.startswith("LeanProofs.Scratch."):
                fail(f"{target.project}/{target.name} imports legacy Scratch: {module} -> {imported}")
                continue

            imported_path = project_dir / module_relpath(imported, src_dir)
            if imported_path.is_file() or imported.split(".", 1)[0] in local_prefixes:
                queue.append(imported)
            elif target.import_policy == "pinned-external":
                # Core Lean modules are supplied by the pinned toolchain, not a
                # package boundary. Everything else is an intentionally locked
                # external closure whose source pin was checked above.
                if imported.split(".", 1)[0] not in {"Init", "Lean", "Std"}:
                    target_external_imports += 1

    if target.import_policy == "pinned-external" and target_external_imports == 0:
        fail(f"pinned-external target reaches no external package import: {target.project}/{target.name}")

    walked_targets += 1
    ownerships += len(seen)
    external_boundaries += target_external_imports
    if target.import_policy == "mathlib-free":
        mathlib_free_targets += 1
    if target.import_policy == "pinned-external":
        pinned_external_targets += 1


for target_name in sorted(stable_roots):
    target = targets.get((".", target_name))
    if target is None or target.role != "stable-surface":
        fail(f"stable-surfaces.tsv names no root-project stable target: {target_name}")


if failures:
    for message in failures:
        print(f"FAIL: {message}", file=sys.stderr)
    print("FAIL: public project/target/import policy does not close", file=sys.stderr)
    raise SystemExit(1)

print(f"PASS — {len(lakefiles)} Lake projects and {len(targets)} public targets registered exactly")
print(f"  exact local target closures walked: {walked_targets}")
print(f"  Mathlib-free current-tree targets:  {mathlib_free_targets}")
print(f"  pinned-external targets:            {pinned_external_targets}")
print(f"  local target/module ownerships:     {ownerships}")
print(f"  locked external import boundaries:  {external_boundaries}")
print("  Mathlib-reaching targets:           explicit-only")
PY
