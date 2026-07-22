#!/usr/bin/env python3
"""Fail-closed qualification for the bounded Someone -> Continuity calculus.

The checker treats the exact Git object containing ``someone/Someone.lean`` as
the frozen source.  It proves that the current checkout still uses that exact
subtree, scans the three owned modules for prohibited source forms, and either
regenerates or verifies a canonical compiled-declaration manifest.

This is deliberately not a general custody framework.  The source policy is
declared once below; generated receipts describe compiled declarations rather
than copying the source revision chain into another checksum rosary.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys
from typing import Any, Iterable


# The one canonical campaign policy input.  Do not duplicate these identities
# in stage wrappers or generated declaration receipts.
POLICY: dict[str, Any] = {
    "campaign_id": "someone-continuity-qualification-2026-07-22",
    "source": {
        "revision": "b00d76535ab6848eb2db80cb68601a07b118c4ef",
        "tree": "8c7e42e8c97659763e5573d063a54fb1d5af1d45",
        "path": "someone/Someone.lean",
        "mode": "100644",
        "blob": "80a71ce18e55515a97567cc9d9f162fd23998ff7",
        "sha256": "efe928e1802218b879867199736fe5dbb5e8dfbddf68dcf09ef499e8077ead44",
    },
    "authorized_base": "600c6f45b8dce82557e2efb99fc77ed234f8e9d5",
    "lean_version": (
        "Lean (version 4.29.0, x86_64-unknown-linux-gnu, "
        "commit 98dc76e3c0a9b856c9b98726b713fb04fab16740, Release)"
    ),
    "build_target": "SomeoneContinuityQualification",
    "dump": "scripts/SomeoneContinuityDeclarationDump.lean",
    "manifest": (
        "docs/someone-continuity-qualification-2026-07-22/"
        "declaration-manifest.json"
    ),
    "modules": {
        "Someone": {
            "path": "someone/Someone.lean",
            "prefix": "Someone",
            "direct_imports": [],
        },
        "ContinuityQualification.Core": {
            "path": "formalization/ContinuityQualification/Core.lean",
            "prefix": "SomeoneContinuityQualification",
            "direct_imports": ["Someone"],
        },
        "ContinuityQualification.Hostile": {
            "path": "formalization/ContinuityQualification/Hostile.lean",
            "prefix": "SomeoneContinuityQualification.Hostile",
            "direct_imports": ["ContinuityQualification.Core"],
        },
    },
    "auxiliary_lean": [
        {
            "path": "formalization/ContinuityQualification.lean",
            "direct_imports": [
                "ContinuityQualification.Core",
                "ContinuityQualification.Hostile",
            ],
        },
        {
            "path": "formalization/ContinuityQualification/Campaign/Qualification.lean",
            "direct_imports": ["ContinuityQualification"],
        },
    ],
}


OID_RE = re.compile(r"^[0-9a-f]{40}$")
SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
SERIALIZATION = "lean-4.29-repr-alpha-level-canonical-v1"
DUMP_SCHEMA = "someone-continuity-compiled-declaration-v1"
MANIFEST_KIND = "someone-continuity-compiled-declarations"
DECLARATION_KINDS = {
    "axiom",
    "definition",
    "theorem",
    "opaque",
    "quotient",
    "inductive",
    "constructor",
    "recursor",
}
ALLOWED_INHERITED_AXIOMS = {"propext", "Quot.sound"}


class CheckError(Exception):
    def __init__(self, code: str, message: str) -> None:
        super().__init__(message)
        self.code = code
        self.message = message


class DuplicateKey(ValueError):
    pass


def reject_duplicate_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise DuplicateKey(key)
        result[key] = value
    return result


def exact_keys(value: Any, keys: Iterable[str], *, where: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise CheckError("SCHEMA", f"{where} must be an object")
    expected = set(keys)
    actual = set(value)
    if actual != expected:
        missing = sorted(expected - actual)
        extra = sorted(actual - expected)
        raise CheckError(
            "SCHEMA",
            f"{where}: missing={missing or '-'} extra={extra or '-'}",
        )
    return value


def require_string(value: Any, where: str) -> str:
    if not isinstance(value, str) or not value:
        raise CheckError("SCHEMA", f"{where} must be a non-empty string")
    return value


def require_nonnegative_int(value: Any, where: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        raise CheckError("SCHEMA", f"{where} must be a nonnegative integer")
    return value


def require_sha256(value: Any, where: str) -> str:
    text = require_string(value, where)
    if SHA256_RE.fullmatch(text) is None:
        raise CheckError("SCHEMA", f"{where} must be a lowercase SHA-256")
    return text


def require_list(value: Any, where: str) -> list[Any]:
    if not isinstance(value, list):
        raise CheckError("SCHEMA", f"{where} must be an array")
    return value


def require_sorted_unique_strings(value: Any, where: str) -> list[str]:
    values = [
        require_string(item, f"{where}[{index}]")
        for index, item in enumerate(require_list(value, where))
    ]
    if values != sorted(values) or len(values) != len(set(values)):
        raise CheckError("AMBIGUOUS", f"{where} must be sorted and unique")
    return values


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def run(
    args: list[str], *, cwd: Path | None = None, check: bool = True
) -> subprocess.CompletedProcess[bytes]:
    process = subprocess.run(
        args,
        cwd=cwd,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if check and process.returncode:
        detail = (process.stdout + process.stderr).decode(
            "utf-8", errors="replace"
        ).strip()
        raise CheckError(
            "COMMAND_FAILED",
            f"{' '.join(args)} failed ({process.returncode}): {detail}",
        )
    return process


class Git:
    def __init__(self, root: Path) -> None:
        self.root = root

    def bytes(self, *args: str) -> bytes:
        return run(["git", "-C", str(self.root), *args]).stdout

    def text(self, *args: str) -> str:
        return self.bytes(*args).decode("utf-8", errors="strict").strip()

    def require_commit(self, oid: str, label: str) -> None:
        if OID_RE.fullmatch(oid) is None:
            raise CheckError("POLICY", f"{label} is not a full lowercase SHA-1")
        if self.text("cat-file", "-t", oid) != "commit":
            raise CheckError("GIT_OBJECT", f"{label} is not a commit: {oid}")
        if self.text("rev-parse", f"{oid}^{{commit}}") != oid:
            raise CheckError("GIT_SUBSTITUTION", f"{label} did not resolve literally")

    def tree(self, revision: str) -> str:
        return self.text("rev-parse", f"{revision}^{{tree}}")

    def object_at(self, revision: str, path: str) -> tuple[str, str, str]:
        raw = self.bytes("ls-tree", "-z", revision, "--", path)
        records = [record for record in raw.split(b"\0") if record]
        if len(records) != 1:
            raise CheckError("GIT_PATH", f"missing or ambiguous: {revision}:{path}")
        metadata, actual_path = records[0].split(b"\t", 1)
        if actual_path.decode("utf-8") != path:
            raise CheckError("GIT_PATH", f"unexpected resolved path for {path}")
        mode, kind, oid = metadata.decode("ascii").split(" ")
        return mode, kind, oid

    def blob(self, oid: str) -> bytes:
        if self.text("cat-file", "-t", oid) != "blob":
            raise CheckError("GIT_OBJECT", f"not a blob: {oid}")
        return self.bytes("cat-file", "blob", oid)

    def is_ancestor(self, ancestor: str, descendant: str) -> bool:
        result = run(
            [
                "git",
                "-C",
                str(self.root),
                "merge-base",
                "--is-ancestor",
                ancestor,
                descendant,
            ],
            check=False,
        )
        if result.returncode == 0:
            return True
        if result.returncode == 1:
            return False
        raise CheckError("GIT_ERROR", "git merge-base --is-ancestor failed")


def canonical_policy_path(value: Any, where: str) -> str:
    text = require_string(value, where)
    parsed = PurePosixPath(text)
    if (
        text.startswith("/")
        or "\\" in text
        or "\0" in text
        or ".." in parsed.parts
        or str(parsed) != text
    ):
        raise CheckError("POLICY_PATH", f"non-canonical path: {text}")
    return text


def verify_source_pin(git: Git, root: Path) -> dict[str, str]:
    source = exact_keys(
        POLICY["source"],
        ("revision", "tree", "path", "mode", "blob", "sha256"),
        where="POLICY.source",
    )
    revision = require_string(source["revision"], "POLICY.source.revision")
    expected_tree = require_string(source["tree"], "POLICY.source.tree")
    path = canonical_policy_path(source["path"], "POLICY.source.path")
    expected_mode = require_string(source["mode"], "POLICY.source.mode")
    expected_blob = require_string(source["blob"], "POLICY.source.blob")
    expected_digest = require_sha256(source["sha256"], "POLICY.source.sha256")
    git.require_commit(revision, "Someone source revision")
    if git.tree(revision) != expected_tree:
        raise CheckError("SOURCE_TREE_DRIFT", revision)
    mode, kind, blob = git.object_at(revision, path)
    if (mode, kind, blob) != (expected_mode, "blob", expected_blob):
        raise CheckError(
            "SOURCE_OBJECT_DRIFT",
            f"expected {expected_mode} blob {expected_blob}, got {mode} {kind} {blob}",
        )
    frozen = git.blob(blob)
    if sha256(frozen) != expected_digest:
        raise CheckError("SOURCE_DIGEST_DRIFT", path)

    base = require_string(POLICY["authorized_base"], "POLICY.authorized_base")
    git.require_commit(base, "authorized qualification base")
    head = git.text("rev-parse", "HEAD^{commit}")
    if not git.is_ancestor(revision, base):
        raise CheckError("SOURCE_ORDER", "source freeze is not an ancestor of base")
    if not git.is_ancestor(base, head):
        raise CheckError("BASE_ANCESTRY", f"{base} is not an ancestor of {head}")

    # This comparison binds the complete source directory without copying a
    # per-file inventory into the campaign checker.
    frozen_subtree = git.text("rev-parse", f"{revision}:someone")
    current_subtree = git.text("rev-parse", f"{head}:someone")
    if current_subtree != frozen_subtree:
        raise CheckError(
            "SOURCE_SUBTREE_DRIFT",
            f"someone subtree {frozen_subtree} became {current_subtree}",
        )
    status = git.text("status", "--porcelain=v1", "--untracked-files=all", "--", "someone")
    if status:
        raise CheckError("SOURCE_WORKTREE_DRIFT", status)
    worktree_path = root / path
    if not worktree_path.is_file() or worktree_path.is_symlink():
        raise CheckError("SOURCE_WORKTREE_DRIFT", str(worktree_path))
    if sha256(worktree_path.read_bytes()) != expected_digest:
        raise CheckError("SOURCE_WORKTREE_DRIFT", path)
    return {
        "revision": revision,
        "tree": expected_tree,
        "blob": expected_blob,
        "sha256": expected_digest,
        "subtree": frozen_subtree,
        "head": head,
    }


def read_direct_imports(path: Path) -> list[str]:
    imports: list[str] = []
    code = lean_code_without_comments_or_strings(path.read_text(encoding="utf-8"))
    for line in code.splitlines():
        stripped = line.strip()
        if stripped.startswith("import "):
            imports.append(stripped.removeprefix("import ").strip())
    return sorted(imports)


def lean_code_without_comments_or_strings(text: str) -> str:
    """Return code tokens while removing nested comments and string contents."""

    output: list[str] = []
    index = 0
    block_depth = 0
    in_line_comment = False
    in_string = False
    escaped = False
    while index < len(text):
        current = text[index]
        following = text[index + 1] if index + 1 < len(text) else ""
        if in_line_comment:
            if current == "\n":
                in_line_comment = False
                output.append("\n")
            else:
                output.append(" ")
            index += 1
            continue
        if block_depth:
            if current == "/" and following == "-":
                block_depth += 1
                output.extend((" ", " "))
                index += 2
            elif current == "-" and following == "/":
                block_depth -= 1
                output.extend((" ", " "))
                index += 2
            else:
                output.append("\n" if current == "\n" else " ")
                index += 1
            continue
        if in_string:
            if escaped:
                escaped = False
            elif current == "\\":
                escaped = True
            elif current == '"':
                in_string = False
            output.append("\n" if current == "\n" else " ")
            index += 1
            continue
        if current == "-" and following == "-":
            in_line_comment = True
            output.extend((" ", " "))
            index += 2
        elif current == "/" and following == "-":
            block_depth = 1
            output.extend((" ", " "))
            index += 2
        elif current == '"':
            in_string = True
            output.append(" ")
            index += 1
        else:
            output.append(current)
            index += 1
    if block_depth or in_string:
        raise CheckError("SOURCE_LEXING", "unterminated comment or string")
    return "".join(output)


PROHIBITED_FORMS: tuple[tuple[str, re.Pattern[str]], ...] = (
    ("sorry", re.compile(r"\bsorry\b")),
    ("admit", re.compile(r"\badmit\b")),
    ("custom axiom", re.compile(r"\baxiom\b")),
    ("Classical", re.compile(r"\bClassical(?:\.choice)?\b")),
    ("choice", re.compile(r"\bchoice\b")),
    ("Quot", re.compile(r"\bQuot(?:ient)?\b")),
    ("native_decide", re.compile(r"\bnative_decide\b")),
    ("unsafe", re.compile(r"\bunsafe\b")),
    ("partial", re.compile(r"\bpartial\b")),
    ("Mathlib import", re.compile(r"(?m)^\s*import\s+Mathlib(?:\.|\s|$)")),
)


def verify_owned_sources(root: Path) -> dict[str, dict[str, str]]:
    modules = exact_keys(
        POLICY["modules"],
        ("Someone", "ContinuityQualification.Core", "ContinuityQualification.Hostile"),
        where="POLICY.modules",
    )
    result: dict[str, dict[str, str]] = {}
    for module, raw_spec in modules.items():
        spec = exact_keys(
            raw_spec,
            ("path", "prefix", "direct_imports"),
            where=f"POLICY.modules.{module}",
        )
        relative = canonical_policy_path(spec["path"], f"{module}.path")
        prefix = require_string(spec["prefix"], f"{module}.prefix")
        expected_imports = sorted(
            require_string(item, f"{module}.direct_imports")
            for item in require_list(spec["direct_imports"], f"{module}.direct_imports")
        )
        path = root / relative
        if not path.is_file() or path.is_symlink():
            raise CheckError("FORMAL_SOURCE_MISSING", relative)
        imports = read_direct_imports(path)
        if imports != expected_imports:
            raise CheckError(
                "IMPORT_DRIFT",
                f"{relative}: expected {expected_imports}, got {imports}",
            )
        content = path.read_bytes()
        code = lean_code_without_comments_or_strings(content.decode("utf-8", errors="strict"))
        for label, pattern in PROHIBITED_FORMS:
            match = pattern.search(code)
            if match is not None:
                line = code.count("\n", 0, match.start()) + 1
                raise CheckError("PROHIBITED_SOURCE_FORM", f"{relative}:{line}: {label}")
        result[module] = {
            "path": relative,
            "prefix": prefix,
            "sha256": sha256(content),
        }
    for index, raw_spec in enumerate(
        require_list(POLICY["auxiliary_lean"], "POLICY.auxiliary_lean")
    ):
        spec = exact_keys(
            raw_spec,
            ("path", "direct_imports"),
            where=f"POLICY.auxiliary_lean[{index}]",
        )
        relative = canonical_policy_path(spec["path"], f"auxiliary[{index}].path")
        path = root / relative
        if not path.is_file() or path.is_symlink():
            raise CheckError("FORMAL_SOURCE_MISSING", relative)
        expected_imports = sorted(
            require_string(item, f"auxiliary[{index}].direct_imports")
            for item in require_list(
                spec["direct_imports"], f"auxiliary[{index}].direct_imports"
            )
        )
        actual_imports = read_direct_imports(path)
        if actual_imports != expected_imports:
            raise CheckError(
                "IMPORT_DRIFT",
                f"{relative}: expected {expected_imports}, got {actual_imports}",
            )
        code = lean_code_without_comments_or_strings(path.read_text(encoding="utf-8"))
        for label, pattern in PROHIBITED_FORMS:
            match = pattern.search(code)
            if match is not None:
                line = code.count("\n", 0, match.start()) + 1
                raise CheckError("PROHIBITED_SOURCE_FORM", f"{relative}:{line}: {label}")
    return result


def declaration_name_matches_owned_surface(
    name: str, source_files: dict[str, dict[str, str]]
) -> bool:
    """Accept names in an owned namespace or Lean's owned private namespace.

    Lean can materialize an equation theorem for an imported definition while
    compiling a later module.  Such a declaration has the imported namespace
    but the later module index, so module-local prefix checking would reject a
    genuine compiled declaration.  The environment module index remains the
    authoritative ownership check; this helper limits names to the union of
    the three selected namespaces.
    """

    for module, source in source_files.items():
        prefix = source["prefix"]
        if (
            name == prefix
            or name.startswith(prefix + ".")
            or name.startswith(f"_private.{module}.")
        ):
            return True
    return False


def declaration_manifest_bytes(
    dump_output: str,
    source_files: dict[str, dict[str, str]],
) -> tuple[bytes, dict[str, Any]]:
    entries: list[dict[str, Any]] = []
    names: set[str] = set()
    by_kind: dict[str, int] = {}
    by_module: dict[str, int] = {}
    by_axiom_footprint: dict[str, int] = {}
    for line_number, line in enumerate(dump_output.splitlines(), 1):
        if not line.strip():
            continue
        try:
            raw = json.loads(line, object_pairs_hook=reject_duplicate_keys)
        except (json.JSONDecodeError, DuplicateKey) as error:
            raise CheckError(
                "DECLARATION_DUMP_MALFORMED", f"line {line_number}: {error}"
            ) from error
        item = exact_keys(
            raw,
            ("schema", "serialization", "module", "name", "kind", "type", "value", "axioms"),
            where=f"dump line {line_number}",
        )
        if item["schema"] != DUMP_SCHEMA or item["serialization"] != SERIALIZATION:
            raise CheckError("DECLARATION_DUMP_MALFORMED", f"line {line_number}: schema")
        module = require_string(item["module"], f"dump[{line_number}].module")
        if module not in source_files:
            raise CheckError("DECLARATION_MODULE_ESCAPE", module)
        name = require_string(item["name"], f"dump[{line_number}].name")
        if name in names:
            raise CheckError("DECLARATION_NAME_AMBIGUOUS", f"duplicate {name}")
        if not declaration_name_matches_owned_surface(name, source_files):
            raise CheckError(
                "DECLARATION_NAME_AMBIGUOUS",
                f"{name} is outside the selected declaration namespaces",
            )
        names.add(name)
        kind = require_string(item["kind"], f"dump[{line_number}].kind")
        if kind not in DECLARATION_KINDS:
            raise CheckError("DECLARATION_KIND", f"{name}: {kind}")
        type_repr = require_string(item["type"], f"dump[{line_number}].type")
        value_repr = item["value"]
        if value_repr is not None and not isinstance(value_repr, str):
            raise CheckError("DECLARATION_DUMP_MALFORMED", f"{name}.value")
        axioms = require_sorted_unique_strings(item["axioms"], f"dump[{line_number}].axioms")
        unexpected_axioms = sorted(set(axioms) - ALLOWED_INHERITED_AXIOMS)
        if unexpected_axioms:
            raise CheckError("AXIOM_DRIFT", f"{name}: {unexpected_axioms}")
        type_digest = sha256(type_repr.encode("utf-8"))
        value_digest = None if value_repr is None else sha256(value_repr.encode("utf-8"))
        axiom_receipt = "AXIOM-FREE" if not axioms else "[" + ", ".join(axioms) + "]"
        content_row = "\t".join(
            [name, kind, type_digest, value_digest or "-", ",".join(axioms)]
        ).encode("utf-8")
        entries.append(
            {
                "name": name,
                "kind": kind,
                "source_module": module,
                "source_path": source_files[module]["path"],
                "normalized_type_sha256": type_digest,
                "normalized_value_sha256": value_digest,
                "normalized_axioms": axioms,
                "normalized_axiom_receipt": axiom_receipt,
                "declaration_content_sha256": sha256(content_row),
            }
        )
        by_kind[kind] = by_kind.get(kind, 0) + 1
        by_module[module] = by_module.get(module, 0) + 1
        by_axiom_footprint[axiom_receipt] = by_axiom_footprint.get(axiom_receipt, 0) + 1
    if not entries:
        raise CheckError("DECLARATION_DUMP_MALFORMED", "empty compiled census")
    entries.sort(key=lambda entry: entry["name"])
    if [entry["name"] for entry in entries] != sorted(names):
        raise CheckError("DECLARATION_NAME_AMBIGUOUS", "declaration ordering")
    source_rows = [
        {
            "module": module,
            "declaration_prefix": source_files[module]["prefix"],
            "path": source_files[module]["path"],
            "sha256": source_files[module]["sha256"],
        }
        for module in sorted(source_files)
    ]
    document: dict[str, Any] = {
        "schema_version": 1,
        "kind": MANIFEST_KIND,
        "campaign_id": POLICY["campaign_id"],
        "serialization": SERIALIZATION,
        "source_files": source_rows,
        "counts": {
            "total": len(entries),
            "by_kind": dict(sorted(by_kind.items())),
            "by_module": dict(sorted(by_module.items())),
            "by_axiom_footprint": dict(sorted(by_axiom_footprint.items())),
            "axiom_free": by_axiom_footprint.get("AXIOM-FREE", 0),
            "axiom_bearing": len(entries) - by_axiom_footprint.get("AXIOM-FREE", 0),
        },
        "declarations": entries,
    }
    data = (json.dumps(document, indent=2, sort_keys=True) + "\n").encode("utf-8")
    return data, document


def load_stored_manifest(path: Path) -> tuple[dict[str, Any], bytes]:
    try:
        raw = path.read_bytes()
        value = json.loads(raw, object_pairs_hook=reject_duplicate_keys)
    except FileNotFoundError as error:
        raise CheckError("MANIFEST_MISSING", str(path)) from error
    except (OSError, UnicodeDecodeError, json.JSONDecodeError, DuplicateKey) as error:
        raise CheckError("MANIFEST_MALFORMED", str(error)) from error
    if not isinstance(value, dict):
        raise CheckError("MANIFEST_SCHEMA", "manifest root must be an object")
    canonical = (json.dumps(value, indent=2, sort_keys=True) + "\n").encode("utf-8")
    if raw != canonical:
        raise CheckError("MANIFEST_NONCANONICAL", str(path))
    return value, raw


def validate_stored_manifest(
    value: dict[str, Any], source_files: dict[str, dict[str, str]]
) -> dict[str, Any]:
    document = exact_keys(
        value,
        (
            "schema_version",
            "kind",
            "campaign_id",
            "serialization",
            "source_files",
            "counts",
            "declarations",
        ),
        where="declaration manifest",
    )
    if (
        document["schema_version"] != 1
        or document["kind"] != MANIFEST_KIND
        or document["campaign_id"] != POLICY["campaign_id"]
        or document["serialization"] != SERIALIZATION
    ):
        raise CheckError("MANIFEST_SCHEMA", "unsupported declaration manifest")
    rows = require_list(document["source_files"], "source_files")
    expected_rows = [
        {
            "module": module,
            "declaration_prefix": source_files[module]["prefix"],
            "path": source_files[module]["path"],
            "sha256": source_files[module]["sha256"],
        }
        for module in sorted(source_files)
    ]
    if rows != expected_rows:
        raise CheckError("MANIFEST_SOURCE_DRIFT", "source file identities differ")
    counts = exact_keys(
        document["counts"],
        (
            "total",
            "by_kind",
            "by_module",
            "by_axiom_footprint",
            "axiom_free",
            "axiom_bearing",
        ),
        where="counts",
    )
    declarations = require_list(document["declarations"], "declarations")
    total = require_nonnegative_int(counts["total"], "counts.total")
    if total != len(declarations):
        raise CheckError("MANIFEST_COUNT_DRIFT", "counts.total")
    axiom_free = require_nonnegative_int(counts["axiom_free"], "counts.axiom_free")
    axiom_bearing = require_nonnegative_int(counts["axiom_bearing"], "counts.axiom_bearing")
    if axiom_free + axiom_bearing != total:
        raise CheckError("MANIFEST_COUNT_DRIFT", "axiom footprint totals")
    names: list[str] = []
    calculated_by_kind: dict[str, int] = {}
    calculated_by_module: dict[str, int] = {}
    calculated_by_axiom_footprint: dict[str, int] = {}
    for index, raw in enumerate(declarations):
        item = exact_keys(
            raw,
            (
                "name",
                "kind",
                "source_module",
                "source_path",
                "normalized_type_sha256",
                "normalized_value_sha256",
                "normalized_axioms",
                "normalized_axiom_receipt",
                "declaration_content_sha256",
            ),
            where=f"declarations[{index}]",
        )
        name = require_string(item["name"], f"declarations[{index}].name")
        names.append(name)
        module = require_string(item["source_module"], f"declarations[{index}].source_module")
        if module not in source_files or item["source_path"] != source_files[module]["path"]:
            raise CheckError("DECLARATION_MODULE_ESCAPE", name)
        if not declaration_name_matches_owned_surface(name, source_files):
            raise CheckError("DECLARATION_NAME_AMBIGUOUS", name)
        kind = require_string(item["kind"], f"declarations[{index}].kind")
        if kind not in DECLARATION_KINDS:
            raise CheckError("DECLARATION_KIND", f"{name}: {kind}")
        type_digest = require_sha256(item["normalized_type_sha256"], f"{name}.type")
        value_digest: str | None = None
        if item["normalized_value_sha256"] is not None:
            value_digest = require_sha256(item["normalized_value_sha256"], f"{name}.value")
        axioms = require_sorted_unique_strings(item["normalized_axioms"], f"{name}.axioms")
        unexpected_axioms = sorted(set(axioms) - ALLOWED_INHERITED_AXIOMS)
        if unexpected_axioms:
            raise CheckError("AXIOM_DRIFT", f"{name}: {unexpected_axioms}")
        expected_receipt = "AXIOM-FREE" if not axioms else "[" + ", ".join(axioms) + "]"
        if item["normalized_axiom_receipt"] != expected_receipt:
            raise CheckError("AXIOM_DRIFT", f"{name}: receipt disagrees")
        content_digest = require_sha256(
            item["declaration_content_sha256"], f"{name}.content"
        )
        content_row = "\t".join(
            [name, kind, type_digest, value_digest or "-", ",".join(axioms)]
        ).encode("utf-8")
        if content_digest != sha256(content_row):
            raise CheckError("DECLARATION_CONTENT_DRIFT", name)
        calculated_by_kind[kind] = calculated_by_kind.get(kind, 0) + 1
        calculated_by_module[module] = calculated_by_module.get(module, 0) + 1
        calculated_by_axiom_footprint[expected_receipt] = (
            calculated_by_axiom_footprint.get(expected_receipt, 0) + 1
        )
    if names != sorted(names) or len(names) != len(set(names)):
        raise CheckError("DECLARATION_NAME_AMBIGUOUS", "names must be sorted and unique")
    if counts["by_kind"] != dict(sorted(calculated_by_kind.items())):
        raise CheckError("MANIFEST_COUNT_DRIFT", "counts.by_kind")
    if counts["by_module"] != dict(sorted(calculated_by_module.items())):
        raise CheckError("MANIFEST_COUNT_DRIFT", "counts.by_module")
    if counts["by_axiom_footprint"] != dict(sorted(calculated_by_axiom_footprint.items())):
        raise CheckError("MANIFEST_COUNT_DRIFT", "counts.by_axiom_footprint")
    if axiom_free != calculated_by_axiom_footprint.get("AXIOM-FREE", 0):
        raise CheckError("MANIFEST_COUNT_DRIFT", "counts.axiom_free")
    if axiom_bearing != total - axiom_free:
        raise CheckError("MANIFEST_COUNT_DRIFT", "counts.axiom_bearing")
    return document


def verify(
    formalization: Path, *, skip_build: bool, write_manifest: bool
) -> dict[str, Any]:
    if skip_build and write_manifest:
        raise CheckError("ARGUMENT", "--write-manifest cannot be combined with --skip-build")
    root = formalization.parent
    git = Git(root)
    source_result = verify_source_pin(git, root)
    source_files = verify_owned_sources(root)
    manifest_relative = canonical_policy_path(POLICY["manifest"], "POLICY.manifest")
    # POLICY paths are relative to the formalization directory except module
    # source paths, which intentionally bind the outer Skunkworks tree.
    manifest_path = formalization / manifest_relative

    if skip_build:
        stored, raw = load_stored_manifest(manifest_path)
        document = validate_stored_manifest(stored, source_files)
        build_status = "SKIPPED"
    else:
        expected_version = require_string(POLICY["lean_version"], "POLICY.lean_version")
        actual_version = run(
            ["lake", "env", "lean", "--version"], cwd=formalization
        ).stdout.decode("utf-8", errors="strict").strip()
        if actual_version != expected_version:
            raise CheckError(
                "LEAN_VERSION_DRIFT",
                f"expected {expected_version!r}, got {actual_version!r}",
            )
        build_target = require_string(POLICY["build_target"], "POLICY.build_target")
        run(["lake", "build", build_target], cwd=formalization)
        dump_path = canonical_policy_path(POLICY["dump"], "POLICY.dump")
        dump = run(["lake", "env", "lean", dump_path], cwd=formalization)
        generated, document = declaration_manifest_bytes(
            dump.stdout.decode("utf-8", errors="strict"), source_files
        )
        if write_manifest:
            manifest_path.parent.mkdir(parents=True, exist_ok=True)
            manifest_path.write_bytes(generated)
        stored, raw = load_stored_manifest(manifest_path)
        validate_stored_manifest(stored, source_files)
        if raw != generated:
            raise CheckError("DECLARATION_MANIFEST_DRIFT", str(manifest_path))
        build_status = "PASS"

    counts = document["counts"]
    return {
        "result": "SOMEONE-CONTINUITY-QUALIFICATION-PASS",
        "campaign_id": POLICY["campaign_id"],
        "source": source_result,
        "build": build_status,
        "modules": sorted(source_files),
        "compiled_declarations": counts["total"],
        "axiom_free": counts["axiom_free"],
        "axiom_bearing": counts["axiom_bearing"],
        "axiom_footprints": counts["by_axiom_footprint"],
        "manifest": str(manifest_path.relative_to(formalization)),
        "manifest_sha256": sha256(raw),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--formalization",
        type=Path,
        default=Path(__file__).resolve().parent.parent,
        help="formalization checkout (default: inferred from this script)",
    )
    parser.add_argument(
        "--skip-build",
        action="store_true",
        help="verify the existing manifest and source pins without invoking Lake or Lean",
    )
    parser.add_argument(
        "--write-manifest",
        action="store_true",
        help="write the regenerated canonical declaration manifest before comparison",
    )
    args = parser.parse_args()
    try:
        result = verify(
            args.formalization.resolve(),
            skip_build=args.skip_build,
            write_manifest=args.write_manifest,
        )
    except CheckError as error:
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
