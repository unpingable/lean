#!/usr/bin/env bash
# Phase 5 — mathlib pin drift check. lakefile.toml's mathlib `rev` must equal the resolved
# commit in lake-manifest.json. Moving mathlib must be explicit (lake update → inspect →
# repin → rerun gates), never silent. Exit: 0 PASS, 2 drift.
set -euo pipefail
REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$REPO_ROOT"

lake_rev="$(awk '
  /name = "mathlib"/ {inblk=1}
  inblk && /rev = / { gsub(/[",]/,""); print $3; exit }
' lakefile.toml)"

man_rev="$(awk '
  /leanprover-community\/mathlib4/ {inblk=1}
  inblk && /"rev":/ { gsub(/[",]/,""); print $2; exit }
' lake-manifest.json)"

echo "lakefile.toml mathlib rev : ${lake_rev:-<none>}"
echo "lake-manifest mathlib rev : ${man_rev:-<none>}"

if [[ -z "${lake_rev:-}" || -z "${man_rev:-}" ]]; then
  echo "FAIL: could not extract one of the revs" >&2; exit 2
fi
if [[ "$lake_rev" == "master" || "$lake_rev" == "main" ]]; then
  echo "FAIL: lakefile.toml mathlib rev is a moving ref ('$lake_rev'); pin to the manifest SHA" >&2; exit 2
fi
if [[ "$lake_rev" != "$man_rev" ]]; then
  echo "FAIL: mathlib pin drift — lakefile ($lake_rev) != manifest ($man_rev)" >&2; exit 2
fi
echo "PASS — mathlib pinned to manifest SHA ($lake_rev)"
