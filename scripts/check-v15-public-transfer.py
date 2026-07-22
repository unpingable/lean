#!/usr/bin/env python3
"""Verify the frozen V15 transfer and its public-custody normalization."""

from __future__ import annotations

import argparse
import csv
import hashlib
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
SOURCE_MANIFEST = ROOT / "docs/V15-PUBLIC-TRANSFER-MANIFEST.tsv"
NORMALIZED_MANIFEST = (
    ROOT / "docs/V15-PUBLIC-CUSTODY-NORMALIZED-BODY-MANIFEST.tsv"
)
SOURCE_MANIFEST_SHA256 = (
    "05a29867a8c9c24996f9a1b975749a61379f32b5b8cdebc9a1100504147d6268"
)
HEADER = (
    b"/-\n"
    b"  Custody-Class: PUBLIC-SHIPPED\n"
    b"  Surface-Role: PUBLIC-EVIDENCE\n"
    b"-/\n"
    b"\n"
)
HEADER_RECORD = (
    r"/-\n  Custody-Class: PUBLIC-SHIPPED\n"
    r"  Surface-Role: PUBLIC-EVIDENCE\n-/\n\n"
)
SOMEONE_PREFIX = b"Private-Source-"
SOMEONE_MARKER = (
    b"  Private-Source-Custody-Class: SCRATCH. Compile-is-contact only. "
    b"Do not promote.\n"
)
NORMALIZED_FIELDS = (
    "private_source_path",
    "public_path",
    "private_full_sha256",
    "public_full_sha256",
    "normalized_public_body_sha256",
    "normalized_matches_precustody",
    "exact_header_inserted",
    "additional_custody_metadata_insertion",
    "import_root_adjustment",
)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git_bytes(repo: str, commit: str, path: str) -> bytes:
    return subprocess.run(
        ["git", "-C", repo, "show", f"{commit}:{path}"],
        check=True,
        stdout=subprocess.PIPE,
    ).stdout


def git_tree(repo: str, commit: str) -> str:
    return subprocess.run(
        ["git", "-C", repo, "rev-parse", f"{commit}^{{tree}}"],
        check=True,
        text=True,
        stdout=subprocess.PIPE,
    ).stdout.strip()


def adjusted_private(data: bytes, adjustment: str) -> bytes:
    if adjustment == "NONE":
        return data
    if adjustment not in {
        "GT_PUBLIC_MODULE_PATH_AND_NAMESPACE_ALPHA_SUBSTITUTION",
        "GT_PUBLIC_NAMESPACE_ALPHA_SUBSTITUTION",
    }:
        raise ValueError(f"unknown source adjustment: {adjustment}")
    result = data.replace(
        b"Calculi.Scratch.GovernedTransport.Hostile",
        b"LeanProofs.GovernedTransport.Hostile",
    ).replace(
        b"Calculi.Scratch.GovernedTransport",
        b"LeanProofs.GovernedTransport",
    )
    result = result.replace(
        b"import LeanProofs.GovernedTransport.Hostile\n",
        b"import LeanProofs.GovernedTransportEvidence.Hostile\n",
    )
    return result


def normalize_public(path: str, data: bytes) -> tuple[bytes, str]:
    if not data.startswith(HEADER):
        raise ValueError(f"{path}: exact public custody header is absent")
    body = data[len(HEADER) :]
    extra = "NONE"
    if path == "someone/Someone.lean":
        if body.count(SOMEONE_MARKER) != 1:
            raise ValueError(f"{path}: private-source marker insertion drift")
        body = body.replace(SOMEONE_PREFIX, b"", 1)
        extra = "REMOVE_INSERTED_PRIVATE_SOURCE_PREFIX"
    return body, extra


def expected_rows() -> list[dict[str, str]]:
    if sha256(SOURCE_MANIFEST.read_bytes()) != SOURCE_MANIFEST_SHA256:
        raise ValueError("frozen private-source transfer manifest digest drift")
    with SOURCE_MANIFEST.open(newline="") as stream:
        source_rows = list(csv.DictReader(stream, delimiter="\t"))

    observed_trees: set[tuple[str, str, str]] = set()
    result: list[dict[str, str]] = []
    lean_count = 0
    for row in source_rows:
        repo = row["private_source_repository"]
        commit = row["source_commit"]
        tree = row["source_tree"]
        tree_key = (repo, commit, tree)
        if tree_key not in observed_trees:
            if git_tree(repo, commit) != tree:
                raise ValueError(f"source tree drift: {repo}@{commit}")
            observed_trees.add(tree_key)

        source = git_bytes(repo, commit, row["source_path"])
        if sha256(source) != row["source_sha256"]:
            raise ValueError(f"private source digest drift: {row['source_path']}")

        public_path = row["public_destination_path"]
        public_file = ROOT / public_path
        if public_path.endswith(".lean"):
            lean_count += 1
            public = public_file.read_bytes()
            normalized, extra = normalize_public(public_path, public)
            if sha256(normalized) != row["destination_sha256"]:
                raise ValueError(f"normalized public body drift: {public_path}")
            transformed = adjusted_private(
                source, row["repository_local_adjustment"]
            )
            if normalized != transformed:
                raise ValueError(f"semantic-body reconstruction drift: {public_path}")
            result.append(
                {
                    "private_source_path": row["source_path"],
                    "public_path": public_path,
                    "private_full_sha256": row["source_sha256"],
                    "public_full_sha256": sha256(public),
                    "normalized_public_body_sha256": sha256(normalized),
                    "normalized_matches_precustody": "true",
                    "exact_header_inserted": HEADER_RECORD,
                    "additional_custody_metadata_insertion": extra,
                    "import_root_adjustment": row[
                        "repository_local_adjustment"
                    ],
                }
            )
        elif public_path != "lakefile.toml":
            if sha256(public_file.read_bytes()) != row["destination_sha256"]:
                raise ValueError(f"transferred non-Lean path drift: {public_path}")

    if lean_count != 56:
        raise ValueError(f"expected 56 transferred Lean files, found {lean_count}")
    return result


def render(rows: list[dict[str, str]]) -> str:
    lines = ["\t".join(NORMALIZED_FIELDS)]
    lines.extend(
        "\t".join(row[field] for field in NORMALIZED_FIELDS) for row in rows
    )
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--write", action="store_true", help="write the derived normalized manifest"
    )
    args = parser.parse_args()
    try:
        expected = render(expected_rows())
        if args.write:
            NORMALIZED_MANIFEST.write_text(expected)
        elif not NORMALIZED_MANIFEST.is_file():
            raise ValueError("normalized-body manifest is missing")
        elif NORMALIZED_MANIFEST.read_text() != expected:
            raise ValueError("normalized-body manifest content drift")
    except (OSError, subprocess.CalledProcessError, ValueError) as error:
        print(f"FAIL: V15 public transfer verification: {error}", file=sys.stderr)
        return 1
    print("PASS — V15 frozen sources and 56 normalized public bodies match exactly")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
