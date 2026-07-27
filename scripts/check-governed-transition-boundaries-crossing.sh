#!/usr/bin/env bash
# V16 candidate source-crossing custody and normalized-body gate.

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$REPO_ROOT"

python3 - "$REPO_ROOT" <<'PY'
from __future__ import annotations

import hashlib
import re
import subprocess
import sys
from pathlib import Path


repo = Path(sys.argv[1]).resolve()
private_commit = "b3d73a7a8f3c47486a29767b8b28c809af0f4e57"
extracted_tree = "84f209f57e2495463833137cd58aac7ce73e6f96"
source_prefix = (
    "formalization/PromotionCandidates/V16GovernedTransitionBoundaries/"
    "Extracted/LeanProofs/"
)

# path -> (surface role, theorem-surface classification, normalized source
# SHA-256, public full-file SHA-256, public Git blob)
expected = {
    "LeanProofs/GovernedTransitionBoundaries.lean": (
        "PUBLIC-EVIDENCE", "GENERIC-CORE-AGGREGATE",
        "db9ffcb21ad439b8d15b96aa1316e608a199d785973139565afd65d30056418c",
        "62e53c24c70dd7d4d2085d6163a7f31f6cc8abfe80a391cc81924bdb2a6621c7",
        "4d609e83bcdf4997b313cc5980ce93f4f237fd40",
    ),
    "LeanProofs/GovernedTransitionBoundaries/Core.lean": (
        "PUBLIC-EVIDENCE", "GENERIC-EXPLICIT-FACTORIZATION-CORE",
        "eb10cbca6b672ebea0f380880dc189bc633aafa8bb635aec7b9c33a7320e261b",
        "00834c3a7421b09c819e70b90b45d487d5fe434a92e4096dea571b0342eca045",
        "25f8b2c3c3520e15167bc0e181766ff425c14a4e",
    ),
    "LeanProofs/GovernedTransitionBoundariesEvidence.lean": (
        "PUBLIC-EVIDENCE", "BOUNDED-EVIDENCE-AGGREGATE",
        "226de883b8017a7f479be445e0bef21206d187298c7e076d7331da81587d96b9",
        "fe15e20648975f9c178fbfee4fa31c5d6278e904e697dd619e66c0aa70468f4c",
        "ccc559636705359e6a66614f5e1d4397954289d8",
    ),
    "LeanProofs/GovernedTransitionBoundariesEvidence/ContextBoundary.lean": (
        "PUBLIC-EVIDENCE", "SELECTED-CONTEXT-VALIDATION-WITNESS",
        "2d29747422d8d6b1e9c57309be096f756981de6fe0cfe450084f426cf94e0a9f",
        "387804a105af1cb2f81bde19b684ebfadd0419278902c863a28015ff6c797ebc",
        "c48156ed1bbf56c498ab340cf992a3219c380566",
    ),
    "LeanProofs/GovernedTransitionBoundariesEvidence/FiniteRepresentation.lean": (
        "PUBLIC-EVIDENCE", "DECLARED-FINITE-COORDINATE-DETERMINACY",
        "a05b753aa28b647003d753ca5c09d2ffa26b6ef13a11276d8943c94cc496d371",
        "74bc37f47b1cd5db7414c8f031d225c1433b3e79e6d0009726de654f0599e8ce",
        "f7aa71b443b381daccbe5b28998f93cfc04d36c5",
    ),
    "LeanProofs/GovernedTransitionBoundariesEvidence/GroundingBoundary.lean": (
        "PUBLIC-EVIDENCE", "MODELED-HIDDEN-RELATION-NONIDENTIFIABILITY-WITNESS",
        "6991a2ba4de6bdab517a7efffea91bbdcd900cdcc24a34100ef198f58bda1e9a",
        "a2fe9a14375b9f90051054b0a411c247e263211254906a811b215306c73f115e",
        "ba26fccf111ee19be716d2def936906d461fb0b4",
    ),
    "LeanProofs/GovernedTransitionBoundariesEvidence/HistoricalBoundary.lean": (
        "PUBLIC-EVIDENCE", "OCCURRENCE-LINK-OBSERVATION-WITNESS",
        "d07cc38cace4d1b09076421622978bfff4a3bad46af78609aa60305a40d9fe4d",
        "2415933395742349b542a3fd0f166555e61d976fcc1ac289f07ab2070b7b9b5b",
        "b6a4a84df2f11ee64ceaaf75c152c9fafea1ac6e",
    ),
    "LeanProofs/GovernedTransitionBoundariesEvidence/JurisdictionBoundary.lean": (
        "PUBLIC-EVIDENCE", "FIXED-POLICY-AUTHORIZATION-REFUSAL-WITNESS",
        "f5817f4b6a77d41f5c9609e16e11953d869739194bb6a41c76f9ab40cab1e4b3",
        "e2b4e225357be36e1a000be7e0123aceca193d66ab320f804a2502025c66e1f8",
        "885bd3caa65cce4c1ab82837501272afe49de9d4",
    ),
    "LeanProofs/GovernedTransitionBoundariesEvidence/Qualification.lean": (
        "PUBLIC-EVIDENCE", "SIGNATURE-AND-AXIOM-FOOTPRINT-GATE",
        "ce7d44e9ee23c830f4afa5f46348072d4e992823e4228dc92a69fce0326eda97",
        "4cfd8e51fff863b66f112ca5453fe86be2b2f194f4416232e4cf8ee2b487b92c",
        "a7770f1a69ab3b9a8bac255f585e70a838d3c559",
    ),
    "LeanProofs/GovernedTransitionBoundariesEvidence/RealizabilityBoundary.lean": (
        "PUBLIC-EVIDENCE", "BOUNDED-CAPACITY-REALIZABILITY-WITNESS",
        "6fa9e29ded25b5ef6cfbfab9460bfa50fed97bf5ac72d3ff0ae4728d08404dc4",
        "a9da012d44e61caaa6e01f44a96e5efbf6d7496c5bddef3019bf54498a3db810",
        "8a5d94126f74ace3bf0a1b7db9008ae020a901dc",
    ),
}

failures: list[str] = []
for relative, (role, theorem_surface, body_sha, full_sha, blob) in expected.items():
    path = repo / relative
    if not path.is_file():
        failures.append(f"missing public destination: {relative}")
        continue
    data = path.read_bytes()
    lines = data.splitlines(keepends=True)
    source_relative = relative.removeprefix("LeanProofs/")
    header = (
        "/-\n"
        "  Custody-Class: PUBLIC-SHIPPED\n"
        f"  Surface-Role: {role}\n"
        "  Private-Source-Repository: unpingable/skunkworks\n"
        f"  Private-Source-Commit: {private_commit}\n"
        f"  Extracted-Tree: {extracted_tree}\n"
        f"  Private-Extracted-Source: {source_prefix}{source_relative}\n"
        f"  Public-Destination: {relative}\n"
        "  Crossing-Campaign-Date: 2026-07-26\n"
        f"  Theorem-Surface: {theorem_surface}\n"
        "-/\n\n"
    ).encode()
    if not data.startswith(header):
        failures.append(f"custody header drift: {relative}")
        continue
    body = data[len(header):]
    if hashlib.sha256(body).hexdigest() != body_sha:
        failures.append(f"normalized extracted body drift: {relative}")
    if hashlib.sha256(data).hexdigest() != full_sha:
        failures.append(f"public full-file hash drift: {relative}")
    actual_blob = subprocess.check_output(
        ["git", "hash-object", str(path)], text=True
    ).strip()
    if actual_blob != blob:
        failures.append(f"public Git blob drift: {relative}")

    text = body.decode()
    if re.search(r"^\s*import\s+.*(?:Skunkworks|PromotionCandidates)", text, re.M):
        failures.append(f"forbidden private import: {relative}")
    if re.search(r"^\s*(?:axiom|constant)\s+", text, re.M):
        failures.append(f"custom axiom/constant declaration: {relative}")
    for token in ("sorry", "unsafe", "native_decide", "Classical.choice"):
        if re.search(rf"\b{re.escape(token)}\b", text):
            failures.append(f"prohibited primitive {token}: {relative}")
    if re.search(r"\badmit\b", text):
        failures.append(f"prohibited primitive admit: {relative}")

if failures:
    for failure in failures:
        print(f"FAIL: {failure}", file=sys.stderr)
    raise SystemExit(1)

print(
    "PASS — 10 public destinations retain exact extracted bodies, exact "
    "custody headers, pinned public hashes/blobs, no private imports, and "
    "no prohibited primitives"
)
PY
