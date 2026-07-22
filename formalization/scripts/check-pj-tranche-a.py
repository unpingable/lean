#!/usr/bin/env python3
"""Fail-closed qualification for the provisional PJ Tranche-A candidate.

One policy block pins the three forcing calculi, the held-out StaticRole
source, the frozen PJ-1 core, exact module imports, and generated receipts.
The checker builds only the isolated PJ target, runs the direct axiom leaf,
and compares a deterministic compiled-declaration manifest.  It does not
ratify PJ or add it to a default/public aggregate.
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


POLICY: dict[str, Any] = {
    "campaign_id": "pj-tranche-a-2026-07-22",
    "authorized_base": "99f3973aca420817ac4eb5a5a1282252326c32e7",
    "lean_version": (
        "Lean (version 4.29.0, x86_64-unknown-linux-gnu, "
        "commit 98dc76e3c0a9b856c9b98726b713fb04fab16740, Release)"
    ),
    "build_target": "PJCrossCalculus",
    "qualification": "PJ/Campaign/TrancheAQualification.lean",
    "dump": "scripts/PJTrancheADeclarationDump.lean",
    "manifest": "PJ/Campaign/declaration-manifest.json",
    "frozen_core_sha256": (
        "1d86bee97f92f2644d8605a05d6a31deaa3584f55582d4a09b638718ffff185c"
    ),
    "sources": {
        "governed_transport": {
            "revision": "71714265062e3b45092c4d79927dfe2ed77dc5fa",
            "tree": "71cb93395a369ce4305288e15b55eb724da0814f",
            "packet_manifest": "formalization/gt4a-export-packet/PACKET-MANIFEST.tsv",
            "packet_sha256": (
                "203f1b54a02469160aee8771a109db77fb812b5bdecd0036c66d066db570d08a"
            ),
            "source_table": "formalization/gt4a-export-packet/source-blobs.tsv",
            "source_table_sha256": (
                "724f1c903302f281934be9ca9da104dfee53d94c5823b1fd85d34239684289b4"
            ),
        },
        "execution_custody": {
            "revision": "9dca58f4587a4a4f5b724662b176af8de3040c04",
            "tree": "7e2b27939bafe7a214085112af2777e395b1b94f",
            "path": "LeanProofs/BoundedCalculi/ExecutionCustody.lean",
            "blob": "5b4b8d00700e8aea2fbe5c94d17e99cdc933a876",
            "sha256": (
                "966d1f6f63d022b13a1ff031fe0558c99e6b2b304ba6f89550d632de14d18aef"
            ),
        },
        "someone_continuity": {
            "source_revision": "b00d76535ab6848eb2db80cb68601a07b118c4ef",
            "source_tree": "8c7e42e8c97659763e5573d063a54fb1d5af1d45",
            "source_subtree": "07a6db31f70bab26c721c350446b69c1fb3b5d13",
            "source_path": "someone/Someone.lean",
            "source_blob": "80a71ce18e55515a97567cc9d9f162fd23998ff7",
            "source_sha256": (
                "efe928e1802218b879867199736fe5dbb5e8dfbddf68dcf09ef499e8077ead44"
            ),
            "qualification_revision": "99f3973aca420817ac4eb5a5a1282252326c32e7",
            "qualification_tree": "843c274726c6094320093e879d6d6288f8a32743",
            "qualification_core_path": "formalization/ContinuityQualification/Core.lean",
            "qualification_core_blob": "5743ca97cc2cb4d1db4d00b399f36a8a31b26743",
            "qualification_core_sha256": (
                "5229bdd2c6965b7592fd0ee03e7af1bff2c76629d9e134b726d9e58d9b566967"
            ),
            "qualification_manifest_path": (
                "formalization/docs/someone-continuity-qualification-2026-07-22/"
                "declaration-manifest.json"
            ),
            "qualification_manifest_sha256": (
                "521c437be1d7f2ac93d0dfded7b368158a339cad8ee004ffb29d41120848c3b9"
            ),
        },
        "static_role": {
            "revision": "0dc621b782b0898152e325633cad1fbcb33b2f01",
            "tree": "f7ff0342aacfc4f0998ebacfd2c3b6b95b748b98",
            "path": "formalization/StaticRole",
            "subtree": "b9ccc98083f302d6d182a65a038d177e60335869",
        },
    },
    "modules": {
        "PJ.Core": {
            "path": "PJ/Core.lean",
            "prefix": "PJ",
            "direct_imports": [],
        },
        "PJ.Hostile": {
            "path": "PJ/Hostile.lean",
            "prefix": "PJ.Hostile",
            "direct_imports": ["PJ.Core"],
        },
        "PJ.Instances.GovernedTransport": {
            "path": "PJ/Instances/GovernedTransport.lean",
            "prefix": "PJ.Instances.GovernedTransport",
            "direct_imports": [
                "PJ.Core",
                "Calculi.Scratch.GovernedTransport.Core",
                "Calculi.Scratch.GovernedTransport.Positive",
                "Calculi.Scratch.GovernedTransport.Negative",
                "Calculi.Scratch.GovernedTransport.Hostile",
            ],
        },
        "PJ.Instances.ExecutionCustody": {
            "path": "PJ/Instances/ExecutionCustody.lean",
            "prefix": "PJ.Instances.ExecutionCustody",
            "direct_imports": [
                "PJ.Core",
                "LeanProofs.BoundedCalculi.ExecutionCustody",
            ],
        },
        "PJ.Instances.SomeoneContinuity": {
            "path": "PJ/Instances/SomeoneContinuity.lean",
            "prefix": "PJ.Instances.SomeoneContinuity",
            "direct_imports": ["PJ.Core", "ContinuityQualification.Core"],
        },
        "PJ.HeldOut.StaticRole": {
            "path": "PJ/HeldOut/StaticRole.lean",
            "prefix": "PJ.HeldOut.StaticRole",
            "direct_imports": [
                "PJ.Core",
                "StaticRole.Theorems.ExpansionIndependence",
                "StaticRole.Theorems.UptakeIndependence",
            ],
        },
    },
    "auxiliary_lean": {
        "PJ.lean": {
            "direct_imports": [
                "PJ.Core",
                "PJ.Hostile",
                "PJ.Instances.GovernedTransport",
                "PJ.Instances.ExecutionCustody",
                "PJ.Instances.SomeoneContinuity",
                "PJ.HeldOut.StaticRole",
            ],
        },
        "PJ/Campaign/TrancheAQualification.lean": {
            "direct_imports": ["PJ", "PJ.HeldOut.StaticRole"],
        },
    },
}


OID_RE = re.compile(r"^[0-9a-f]{40}$")
SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
PRINT_FREE_RE = re.compile(r"^'([^']+)' does not depend on any axioms$")
PRINT_AXIOMS_RE = re.compile(r"^'([^']+)' depends on axioms: \[(.*)\]$")
PRINT_SOURCE_RE = re.compile(r"^\s*#print\s+axioms\s+([A-Za-z0-9_'.]+)\s*$")
SERIALIZATION = "lean-4.29-repr-alpha-level-canonical-v1"
DUMP_SCHEMA = "pj-tranche-a-compiled-declaration-v1"
MANIFEST_KIND = "pj-tranche-a-compiled-declarations"
ALLOWED_INHERITED_AXIOMS = {"propext", "Quot.sound"}
DECLARATION_KINDS = {
    "axiom", "definition", "theorem", "opaque", "quotient",
    "inductive", "constructor", "recursor",
}


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


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def run(args: list[str], *, cwd: Path, check: bool = True) -> subprocess.CompletedProcess[bytes]:
    process = subprocess.run(
        args, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False
    )
    if check and process.returncode:
        detail = (process.stdout + process.stderr).decode("utf-8", errors="replace").strip()
        raise CheckError(
            "COMMAND_FAILED", f"{' '.join(args)} failed ({process.returncode}): {detail}"
        )
    return process


class Git:
    def __init__(self, root: Path) -> None:
        self.root = root

    def bytes(self, *args: str) -> bytes:
        return run(["git", *args], cwd=self.root).stdout

    def text(self, *args: str) -> str:
        return self.bytes(*args).decode("utf-8", errors="strict").strip()

    def require_commit(self, revision: str, expected_tree: str, label: str) -> None:
        if OID_RE.fullmatch(revision) is None or OID_RE.fullmatch(expected_tree) is None:
            raise CheckError("POLICY", f"{label}: malformed Git identity")
        if self.text("cat-file", "-t", revision) != "commit":
            raise CheckError("GIT_OBJECT", f"{label}: {revision} is not a commit")
        if self.text("rev-parse", f"{revision}^{{commit}}") != revision:
            raise CheckError("GIT_SUBSTITUTION", label)
        actual_tree = self.text("rev-parse", f"{revision}^{{tree}}")
        if actual_tree != expected_tree:
            raise CheckError("TREE_DRIFT", f"{label}: {actual_tree}")

    def object_at(self, revision: str, path: str) -> tuple[str, str, str]:
        raw = self.bytes("ls-tree", "-z", revision, "--", path)
        records = [record for record in raw.split(b"\0") if record]
        if len(records) != 1:
            raise CheckError("GIT_PATH", f"missing or ambiguous: {revision}:{path}")
        metadata, actual = records[0].split(b"\t", 1)
        if actual.decode("utf-8") != path:
            raise CheckError("GIT_PATH", path)
        mode, kind, oid = metadata.decode("ascii").split(" ")
        return mode, kind, oid

    def blob_at(self, revision: str, path: str) -> tuple[str, bytes]:
        mode, kind, oid = self.object_at(revision, path)
        if mode != "100644" or kind != "blob":
            raise CheckError("GIT_PATH_TYPE", f"{revision}:{path}: {mode} {kind}")
        return oid, self.bytes("cat-file", "blob", oid)

    def is_ancestor(self, ancestor: str, descendant: str) -> bool:
        result = run(
            ["git", "merge-base", "--is-ancestor", ancestor, descendant],
            cwd=self.root,
            check=False,
        )
        if result.returncode == 0:
            return True
        if result.returncode == 1:
            return False
        raise CheckError("GIT_ERROR", "git merge-base --is-ancestor failed")


def canonical_path(value: str) -> str:
    parsed = PurePosixPath(value)
    if (
        not value or value.startswith("/") or "\\" in value or "\0" in value
        or ".." in parsed.parts or str(parsed) != value
    ):
        raise CheckError("POLICY_PATH", value)
    return value


def require_file_digest(root: Path, relative: str, expected: str) -> bytes:
    if SHA256_RE.fullmatch(expected) is None:
        raise CheckError("POLICY", f"malformed SHA-256 for {relative}")
    path = root / canonical_path(relative)
    if not path.is_file() or path.is_symlink():
        raise CheckError("SOURCE_WORKTREE_DRIFT", relative)
    data = path.read_bytes()
    if sha256(data) != expected:
        raise CheckError("SOURCE_DIGEST_DRIFT", relative)
    return data


def require_clean_path(git: Git, path: str) -> None:
    status = git.text("status", "--porcelain=v1", "--untracked-files=all", "--", path)
    if status:
        raise CheckError("SOURCE_WORKTREE_DRIFT", status)


def parse_gt_source_table(data: bytes) -> list[tuple[str, str]]:
    """Read the one canonical GT packet inventory without copying its rows.

    The table digest is pinned in policy.  Parsing it here turns that single
    authoritative inventory into exact path/blob checks while avoiding a
    second, stage-local checksum rosary.
    """

    try:
        text = data.decode("utf-8", errors="strict")
    except UnicodeDecodeError as error:
        raise CheckError("GT_SOURCE_TABLE_MALFORMED", str(error)) from error
    rows: list[tuple[str, str]] = []
    seen: set[str] = set()
    for line_number, line in enumerate(text.splitlines(), 1):
        fields = line.split("\t")
        if len(fields) != 5:
            raise CheckError("GT_SOURCE_TABLE_MALFORMED", f"line {line_number}")
        mode, blob, source_revision, classification, relative = fields
        if (
            mode != "100644"
            or OID_RE.fullmatch(blob) is None
            or OID_RE.fullmatch(source_revision) is None
            or classification not in {
                "STABLE-SURFACE", "STABLE-WITH-EVIDENCE-SPLIT", "PUBLIC-EVIDENCE"
            }
            or not relative.startswith("Calculi/Scratch/GovernedTransport/")
            or not relative.endswith(".lean")
            or relative in seen
        ):
            raise CheckError("GT_SOURCE_TABLE_MALFORMED", f"line {line_number}")
        canonical_path(relative)
        seen.add(relative)
        rows.append((relative, blob))
    if not rows:
        raise CheckError("GT_SOURCE_TABLE_MALFORMED", "empty table")
    return rows


def verify_outer_sources(formalization: Path) -> dict[str, Any]:
    root = formalization.parent
    git = Git(root)
    head = git.text("rev-parse", "HEAD^{commit}")
    base = POLICY["authorized_base"]
    git.require_commit(base, "843c274726c6094320093e879d6d6288f8a32743", "PJ authorized base")
    if not git.is_ancestor(base, head):
        raise CheckError("BASE_ANCESTRY", f"{base} is not an ancestor of {head}")

    gt = POLICY["sources"]["governed_transport"]
    git.require_commit(gt["revision"], gt["tree"], "GT-4A source custody")
    packet_oid, packet = git.blob_at(gt["revision"], gt["packet_manifest"])
    del packet_oid
    if sha256(packet) != gt["packet_sha256"]:
        raise CheckError("GT_PACKET_DRIFT", gt["packet_manifest"])
    require_file_digest(root, gt["packet_manifest"], gt["packet_sha256"])
    table_oid, table = git.blob_at(gt["revision"], gt["source_table"])
    del table_oid
    if sha256(table) != gt["source_table_sha256"]:
        raise CheckError("GT_SOURCE_TABLE_DRIFT", gt["source_table"])
    require_file_digest(root, gt["source_table"], gt["source_table_sha256"])
    for relative, expected_blob in parse_gt_source_table(table):
        path = "formalization/" + relative
        actual_blob, frozen = git.blob_at(gt["revision"], path)
        if actual_blob != expected_blob:
            raise CheckError("GT_SOURCE_BLOB_DRIFT", path)
        worktree = root / path
        if not worktree.is_file() or worktree.is_symlink() or worktree.read_bytes() != frozen:
            raise CheckError("GT_SOURCE_WORKTREE_DRIFT", path)
        require_clean_path(git, path)

    someone = POLICY["sources"]["someone_continuity"]
    git.require_commit(
        someone["source_revision"], someone["source_tree"], "Someone frozen source"
    )
    if git.text("rev-parse", f"{someone['source_revision']}:someone") != someone["source_subtree"]:
        raise CheckError("SOMEONE_SUBTREE_DRIFT", someone["source_revision"])
    if git.text("rev-parse", f"{head}:someone") != someone["source_subtree"]:
        raise CheckError("SOMEONE_SUBTREE_DRIFT", head)
    source_oid, source_data = git.blob_at(someone["source_revision"], someone["source_path"])
    if source_oid != someone["source_blob"] or sha256(source_data) != someone["source_sha256"]:
        raise CheckError("SOMEONE_SOURCE_DRIFT", someone["source_path"])
    require_file_digest(root, someone["source_path"], someone["source_sha256"])
    require_clean_path(git, "someone")

    git.require_commit(
        someone["qualification_revision"],
        someone["qualification_tree"],
        "Someone qualification ratification",
    )
    core_oid, core_data = git.blob_at(
        someone["qualification_revision"], someone["qualification_core_path"]
    )
    if (
        core_oid != someone["qualification_core_blob"]
        or sha256(core_data) != someone["qualification_core_sha256"]
    ):
        raise CheckError("SOMEONE_QUALIFICATION_DRIFT", someone["qualification_core_path"])
    require_file_digest(root, someone["qualification_core_path"], someone["qualification_core_sha256"])
    require_file_digest(
        root,
        someone["qualification_manifest_path"],
        someone["qualification_manifest_sha256"],
    )
    require_clean_path(git, someone["qualification_core_path"])
    require_clean_path(git, someone["qualification_manifest_path"])

    static = POLICY["sources"]["static_role"]
    git.require_commit(static["revision"], static["tree"], "StaticRole phase-three ratification")
    if git.text("rev-parse", f"{static['revision']}:{static['path']}") != static["subtree"]:
        raise CheckError("STATIC_ROLE_SUBTREE_DRIFT", static["revision"])
    if git.text("rev-parse", f"{head}:{static['path']}") != static["subtree"]:
        raise CheckError("STATIC_ROLE_SUBTREE_DRIFT", head)
    require_clean_path(git, static["path"])

    return {
        "head": head,
        "governed_transport": {
            "revision": gt["revision"],
            "tree": gt["tree"],
            "packet_sha256": gt["packet_sha256"],
        },
        "someone_continuity": {
            "source_revision": someone["source_revision"],
            "source_tree": someone["source_tree"],
            "qualification_revision": someone["qualification_revision"],
            "qualification_tree": someone["qualification_tree"],
        },
        "static_role": {"revision": static["revision"], "tree": static["tree"]},
    }


def verify_execution_source(formalization: Path) -> dict[str, str]:
    source = POLICY["sources"]["execution_custody"]
    public_root = formalization.parent.parent / "lean"
    git = Git(public_root)
    git.require_commit(source["revision"], source["tree"], "Execution Custody public source")
    oid, frozen = git.blob_at(source["revision"], source["path"])
    if oid != source["blob"] or sha256(frozen) != source["sha256"]:
        raise CheckError("EXECUTION_SOURCE_DRIFT", source["path"])
    require_file_digest(public_root, source["path"], source["sha256"])
    require_clean_path(git, source["path"])
    return {
        "revision": source["revision"], "tree": source["tree"],
        "blob": source["blob"], "sha256": source["sha256"],
    }


def lean_code_without_comments_or_strings(text: str) -> str:
    output: list[str] = []
    index = 0
    block_depth = 0
    line_comment = False
    string = False
    escaped = False
    while index < len(text):
        current = text[index]
        following = text[index + 1] if index + 1 < len(text) else ""
        if line_comment:
            if current == "\n":
                line_comment = False
                output.append("\n")
            else:
                output.append(" ")
            index += 1
        elif block_depth:
            if current == "/" and following == "-":
                block_depth += 1; output.extend((" ", " ")); index += 2
            elif current == "-" and following == "/":
                block_depth -= 1; output.extend((" ", " ")); index += 2
            else:
                output.append("\n" if current == "\n" else " "); index += 1
        elif string:
            if escaped:
                escaped = False
            elif current == "\\":
                escaped = True
            elif current == '"':
                string = False
            output.append("\n" if current == "\n" else " "); index += 1
        elif current == "-" and following == "-":
            line_comment = True; output.extend((" ", " ")); index += 2
        elif current == "/" and following == "-":
            block_depth = 1; output.extend((" ", " ")); index += 2
        elif current == '"':
            string = True; output.append(" "); index += 1
        else:
            output.append(current); index += 1
    if block_depth or string:
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
    ("Mathlib", re.compile(r"(?m)^\s*import\s+Mathlib(?:\.|\s|$)")),
)


def read_direct_imports(code: str) -> list[str]:
    imports: list[str] = []
    for line in code.splitlines():
        stripped = line.strip()
        if stripped.startswith("import "):
            imports.append(stripped.removeprefix("import ").strip())
    return sorted(imports)


def verify_lean_file(path: Path, expected_imports: list[str]) -> str:
    if not path.is_file() or path.is_symlink():
        raise CheckError("FORMAL_SOURCE_MISSING", str(path))
    content = path.read_bytes()
    code = lean_code_without_comments_or_strings(content.decode("utf-8", errors="strict"))
    imports = read_direct_imports(code)
    if imports != sorted(expected_imports):
        raise CheckError("IMPORT_DRIFT", f"{path}: expected {sorted(expected_imports)}, got {imports}")
    for label, pattern in PROHIBITED_FORMS:
        match = pattern.search(code)
        if match is not None:
            line = code.count("\n", 0, match.start()) + 1
            raise CheckError("PROHIBITED_SOURCE_FORM", f"{path}:{line}: {label}")
    return sha256(content)


def verify_owned_sources(formalization: Path) -> dict[str, dict[str, str]]:
    result: dict[str, dict[str, str]] = {}
    for module, spec in POLICY["modules"].items():
        relative = canonical_path(spec["path"])
        digest = verify_lean_file(formalization / relative, spec["direct_imports"])
        result[module] = {"path": relative, "prefix": spec["prefix"], "sha256": digest}
    if result["PJ.Core"]["sha256"] != POLICY["frozen_core_sha256"]:
        raise CheckError("PJ_CORE_DRIFT", result["PJ.Core"]["sha256"])
    for relative, spec in POLICY["auxiliary_lean"].items():
        verify_lean_file(formalization / canonical_path(relative), spec["direct_imports"])
    return result


def qualification_declarations(path: Path) -> list[str]:
    code = lean_code_without_comments_or_strings(path.read_text(encoding="utf-8"))
    declarations: list[str] = []
    for line in code.splitlines():
        match = PRINT_SOURCE_RE.fullmatch(line)
        if match is not None:
            declarations.append(match.group(1))
    if not declarations or declarations != list(dict.fromkeys(declarations)):
        raise CheckError("QUALIFICATION_LEAF", "central declarations must be nonempty and unique")
    return declarations


def parse_axiom_receipts(output: str, expected: list[str]) -> dict[str, list[str]]:
    receipts: dict[str, list[str]] = {}
    for line in output.splitlines():
        free = PRINT_FREE_RE.fullmatch(line.strip())
        bearing = PRINT_AXIOMS_RE.fullmatch(line.strip())
        if free:
            name, axioms = free.group(1), []
        elif bearing:
            name = bearing.group(1)
            payload = bearing.group(2).strip()
            axioms = [] if not payload else [part.strip() for part in payload.split(",")]
        else:
            continue
        if name in receipts:
            raise CheckError("AXIOM_RECEIPT", f"duplicate receipt: {name}")
        unexpected = sorted(set(axioms) - ALLOWED_INHERITED_AXIOMS)
        if unexpected:
            raise CheckError("AXIOM_DRIFT", f"{name}: {unexpected}")
        receipts[name] = axioms
    if set(receipts) != set(expected):
        raise CheckError(
            "AXIOM_RECEIPT", f"missing={sorted(set(expected)-set(receipts))} extra={sorted(set(receipts)-set(expected))}"
        )
    return receipts


def declaration_name_matches(name: str, module: str, source_files: dict[str, dict[str, str]]) -> bool:
    prefix = source_files[module]["prefix"]
    return (
        name == prefix or name.startswith(prefix + ".")
        or name.startswith(f"_private.{module}.")
    )


def declaration_manifest_bytes(
    dump_output: str, source_files: dict[str, dict[str, str]], source_pins: dict[str, Any]
) -> tuple[bytes, dict[str, Any]]:
    entries: list[dict[str, Any]] = []
    names: set[str] = set()
    by_kind: dict[str, int] = {}
    by_module: dict[str, int] = {}
    by_axioms: dict[str, int] = {}
    for line_number, line in enumerate(dump_output.splitlines(), 1):
        if not line.strip():
            continue
        try:
            item = json.loads(line, object_pairs_hook=reject_duplicate_keys)
        except (json.JSONDecodeError, DuplicateKey) as error:
            raise CheckError("DECLARATION_DUMP_MALFORMED", f"line {line_number}: {error}") from error
        expected_keys = {"schema", "serialization", "module", "name", "kind", "type", "value", "axioms"}
        if not isinstance(item, dict) or set(item) != expected_keys:
            raise CheckError("DECLARATION_DUMP_MALFORMED", f"line {line_number}: fields")
        if item["schema"] != DUMP_SCHEMA or item["serialization"] != SERIALIZATION:
            raise CheckError("DECLARATION_DUMP_MALFORMED", f"line {line_number}: schema")
        module, name, kind = item["module"], item["name"], item["kind"]
        if module not in source_files or not isinstance(name, str) or not declaration_name_matches(name, module, source_files):
            raise CheckError("DECLARATION_MODULE_ESCAPE", f"{module}:{name}")
        if name in names:
            raise CheckError("DECLARATION_NAME_AMBIGUOUS", name)
        names.add(name)
        if kind not in DECLARATION_KINDS:
            raise CheckError("DECLARATION_KIND", f"{name}:{kind}")
        if not isinstance(item["type"], str) or not item["type"]:
            raise CheckError("DECLARATION_DUMP_MALFORMED", f"{name}.type")
        if item["value"] is not None and not isinstance(item["value"], str):
            raise CheckError("DECLARATION_DUMP_MALFORMED", f"{name}.value")
        axioms = item["axioms"]
        if not isinstance(axioms, list) or not all(isinstance(a, str) for a in axioms) or axioms != sorted(set(axioms)):
            raise CheckError("DECLARATION_DUMP_MALFORMED", f"{name}.axioms")
        unexpected = sorted(set(axioms) - ALLOWED_INHERITED_AXIOMS)
        if unexpected:
            raise CheckError("AXIOM_DRIFT", f"{name}: {unexpected}")
        type_digest = sha256(item["type"].encode())
        value_digest = None if item["value"] is None else sha256(item["value"].encode())
        receipt = "AXIOM-FREE" if not axioms else "[" + ", ".join(axioms) + "]"
        row = "\t".join([name, kind, type_digest, value_digest or "-", ",".join(axioms)]).encode()
        entries.append({
            "name": name, "kind": kind, "source_module": module,
            "source_path": source_files[module]["path"],
            "normalized_type_sha256": type_digest,
            "normalized_value_sha256": value_digest,
            "normalized_axioms": axioms,
            "normalized_axiom_receipt": receipt,
            "declaration_content_sha256": sha256(row),
        })
        by_kind[kind] = by_kind.get(kind, 0) + 1
        by_module[module] = by_module.get(module, 0) + 1
        by_axioms[receipt] = by_axioms.get(receipt, 0) + 1
    if not entries:
        raise CheckError("DECLARATION_DUMP_MALFORMED", "empty census")
    entries.sort(key=lambda item: item["name"])
    source_rows = [
        {"module": module, "declaration_prefix": source_files[module]["prefix"],
         "path": source_files[module]["path"], "sha256": source_files[module]["sha256"]}
        for module in sorted(source_files)
    ]
    axiom_free = by_axioms.get("AXIOM-FREE", 0)
    document = {
        "schema_version": 1,
        "kind": MANIFEST_KIND,
        "campaign_id": POLICY["campaign_id"],
        "serialization": SERIALIZATION,
        "source_pins": source_pins,
        "source_files": source_rows,
        "counts": {
            "total": len(entries), "axiom_free": axiom_free,
            "axiom_bearing": len(entries) - axiom_free,
            "by_kind": dict(sorted(by_kind.items())),
            "by_module": dict(sorted(by_module.items())),
            "by_axiom_footprint": dict(sorted(by_axioms.items())),
        },
        "declarations": entries,
    }
    data = (json.dumps(document, indent=2, sort_keys=True) + "\n").encode()
    return data, document


def load_canonical_json(path: Path) -> tuple[dict[str, Any], bytes]:
    try:
        raw = path.read_bytes()
        value = json.loads(raw, object_pairs_hook=reject_duplicate_keys)
    except (OSError, json.JSONDecodeError, DuplicateKey) as error:
        raise CheckError("MANIFEST_MALFORMED", str(error)) from error
    if not isinstance(value, dict):
        raise CheckError("MANIFEST_MALFORMED", "root is not an object")
    canonical = (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()
    if raw != canonical:
        raise CheckError("MANIFEST_NONCANONICAL", str(path))
    return value, raw


def validate_manifest(
    document: dict[str, Any],
    source_files: dict[str, dict[str, str]],
    source_pins: dict[str, Any],
) -> None:
    expected_top = {
        "schema_version", "kind", "campaign_id", "serialization",
        "source_pins", "source_files", "counts", "declarations",
    }
    if set(document) != expected_top:
        raise CheckError("MANIFEST_SCHEMA", "top-level fields")
    if (
        document["schema_version"] != 1
        or document["kind"] != MANIFEST_KIND
        or document["campaign_id"] != POLICY["campaign_id"]
        or document["serialization"] != SERIALIZATION
        or document["source_pins"] != source_pins
    ):
        raise CheckError("MANIFEST_SOURCE_DRIFT", "header or source pins")
    expected_source_rows = [
        {"module": module, "declaration_prefix": source_files[module]["prefix"],
         "path": source_files[module]["path"], "sha256": source_files[module]["sha256"]}
        for module in sorted(source_files)
    ]
    if document["source_files"] != expected_source_rows:
        raise CheckError("MANIFEST_SOURCE_DRIFT", "owned source rows")
    counts = document["counts"]
    expected_count_keys = {
        "total", "axiom_free", "axiom_bearing", "by_kind", "by_module",
        "by_axiom_footprint",
    }
    if not isinstance(counts, dict) or set(counts) != expected_count_keys:
        raise CheckError("MANIFEST_SCHEMA", "counts")
    declarations = document["declarations"]
    if not isinstance(declarations, list):
        raise CheckError("MANIFEST_SCHEMA", "declarations")
    expected_decl_keys = {
        "name", "kind", "source_module", "source_path",
        "normalized_type_sha256", "normalized_value_sha256",
        "normalized_axioms", "normalized_axiom_receipt",
        "declaration_content_sha256",
    }
    names: list[str] = []
    by_kind: dict[str, int] = {}
    by_module: dict[str, int] = {}
    by_axioms: dict[str, int] = {}
    for index, item in enumerate(declarations):
        if not isinstance(item, dict) or set(item) != expected_decl_keys:
            raise CheckError("MANIFEST_SCHEMA", f"declarations[{index}]")
        name, kind, module = item["name"], item["kind"], item["source_module"]
        if not isinstance(name, str) or not name:
            raise CheckError("MANIFEST_SCHEMA", f"declarations[{index}].name")
        if module not in source_files or not declaration_name_matches(name, module, source_files):
            raise CheckError("DECLARATION_MODULE_ESCAPE", name)
        if item["source_path"] != source_files[module]["path"]:
            raise CheckError("DECLARATION_MODULE_ESCAPE", name)
        if kind not in DECLARATION_KINDS:
            raise CheckError("DECLARATION_KIND", f"{name}:{kind}")
        type_digest = item["normalized_type_sha256"]
        value_digest = item["normalized_value_sha256"]
        content_digest = item["declaration_content_sha256"]
        if not isinstance(type_digest, str) or SHA256_RE.fullmatch(type_digest) is None:
            raise CheckError("MANIFEST_SCHEMA", f"{name}.type")
        if value_digest is not None and (
            not isinstance(value_digest, str) or SHA256_RE.fullmatch(value_digest) is None
        ):
            raise CheckError("MANIFEST_SCHEMA", f"{name}.value")
        if not isinstance(content_digest, str) or SHA256_RE.fullmatch(content_digest) is None:
            raise CheckError("MANIFEST_SCHEMA", f"{name}.content")
        axioms = item["normalized_axioms"]
        if (
            not isinstance(axioms, list)
            or not all(isinstance(axiom, str) for axiom in axioms)
            or axioms != sorted(set(axioms))
            or set(axioms) - ALLOWED_INHERITED_AXIOMS
        ):
            raise CheckError("AXIOM_DRIFT", name)
        receipt = "AXIOM-FREE" if not axioms else "[" + ", ".join(axioms) + "]"
        if item["normalized_axiom_receipt"] != receipt:
            raise CheckError("AXIOM_DRIFT", f"{name}: receipt")
        row = "\t".join(
            [name, kind, type_digest, value_digest or "-", ",".join(axioms)]
        ).encode()
        if content_digest != sha256(row):
            raise CheckError("DECLARATION_CONTENT_DRIFT", name)
        names.append(name)
        by_kind[kind] = by_kind.get(kind, 0) + 1
        by_module[module] = by_module.get(module, 0) + 1
        by_axioms[receipt] = by_axioms.get(receipt, 0) + 1
    if names != sorted(names) or len(names) != len(set(names)):
        raise CheckError("DECLARATION_NAME_AMBIGUOUS", "manifest ordering")
    expected_counts = {
        "total": len(declarations),
        "axiom_free": by_axioms.get("AXIOM-FREE", 0),
        "axiom_bearing": len(declarations) - by_axioms.get("AXIOM-FREE", 0),
        "by_kind": dict(sorted(by_kind.items())),
        "by_module": dict(sorted(by_module.items())),
        "by_axiom_footprint": dict(sorted(by_axioms.items())),
    }
    if counts != expected_counts:
        raise CheckError("MANIFEST_COUNT_DRIFT", "compiled declaration counts")


def verify(
    formalization: Path, *, skip_build: bool, write_manifest: bool
) -> dict[str, Any]:
    if skip_build and write_manifest:
        raise CheckError("ARGUMENT", "--skip-build and --write-manifest are incompatible")
    outer = verify_outer_sources(formalization)
    execution = verify_execution_source(formalization)
    source_files = verify_owned_sources(formalization)
    source_pins = {
        "execution_custody": execution,
        "governed_transport": outer["governed_transport"],
        "someone_continuity": outer["someone_continuity"],
        "static_role": outer["static_role"],
    }
    manifest_path = formalization / POLICY["manifest"]
    expected_central = qualification_declarations(formalization / POLICY["qualification"])

    if skip_build:
        document, raw = load_canonical_json(manifest_path)
        validate_manifest(document, source_files, source_pins)
        receipts: dict[str, list[str]] = {}
        build_status = "SKIPPED"
    else:
        actual_version = run(["lake", "env", "lean", "--version"], cwd=formalization).stdout.decode().strip()
        if actual_version != POLICY["lean_version"]:
            raise CheckError("LEAN_VERSION_DRIFT", actual_version)
        run(["lake", "build", POLICY["build_target"]], cwd=formalization)
        qualification = run(
            ["lake", "env", "lean", POLICY["qualification"]], cwd=formalization
        )
        receipts = parse_axiom_receipts(qualification.stdout.decode(), expected_central)
        dump = run(["lake", "env", "lean", POLICY["dump"]], cwd=formalization)
        generated, document = declaration_manifest_bytes(
            dump.stdout.decode(), source_files, source_pins
        )
        if write_manifest:
            manifest_path.parent.mkdir(parents=True, exist_ok=True)
            manifest_path.write_bytes(generated)
        stored, raw = load_canonical_json(manifest_path)
        validate_manifest(stored, source_files, source_pins)
        if raw != generated or stored != document:
            raise CheckError("DECLARATION_MANIFEST_DRIFT", str(manifest_path))
        build_status = "PASS"

    counts = document.get("counts")
    if not isinstance(counts, dict) or not isinstance(counts.get("total"), int):
        raise CheckError("MANIFEST_MALFORMED", "counts")
    return {
        "result": "PJ-TRANCHE-A-QUALIFICATION-PASS",
        "campaign_id": POLICY["campaign_id"],
        "head": outer["head"],
        "build": build_status,
        "sources": source_pins,
        "frozen_core_sha256": source_files["PJ.Core"]["sha256"],
        "modules": sorted(source_files),
        "central_receipts": len(expected_central),
        "central_axiom_free": sum(not axioms for axioms in receipts.values()) if receipts else None,
        "compiled_declarations": counts["total"],
        "axiom_footprints": counts.get("by_axiom_footprint"),
        "manifest": POLICY["manifest"],
        "manifest_sha256": sha256(raw),
    }


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
    except CheckError as error:
        print(json.dumps({"result": "FAIL", "code": error.code, "message": error.message}, sort_keys=True), file=sys.stderr)
        return 1
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
