#!/usr/bin/env bash
# Guard the cheap custody target. `AdmissibilityCustodyAnnex` is promised
# Mathlib-free (Admissibility/README.md, 2026-07-08 import-surface split):
# public kernels plus the ANNEX modules that do NOT cross into the
# Finset-backed cross-boundary/composition island. This script walks the
# static import closure of the target's roots (as declared in lakefile.toml)
# and fails closed if the closure imports Mathlib or reaches one of the
# named heavy roots. Exit code is the gate, never eyeballed.
#
# Exit codes:
#   0 — closure is Mathlib-free and avoids all heavy roots
#   1 — could not extract the target's roots from lakefile.toml
#   2 — a module in the closure imports Mathlib
#   3 — the closure reaches a module reserved to AdmissibilityMathlibIslands
#   4 — a root or imported LeanProofs module has no source file on disk

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$REPO_ROOT"

TARGET="AdmissibilityCustodyAnnex"

# Modules reserved to the explicit heavy island (AdmissibilityMathlibIslands).
HEAVY=(
  LeanProofs.Admissibility.CrossBoundaryExposure
  LeanProofs.Admissibility.CrossBoundaryDegradation
  LeanProofs.Admissibility.CrossBoundaryFailureMint
  LeanProofs.Admissibility.CrossBoundaryCascade
  LeanProofs.Admissibility.Composition
  LeanProofs.Admissibility.LocalBoundary
)

# 1. Extract the target's roots from lakefile.toml.
roots=$(awk -v target="$TARGET" '
  /^name = / { in_target = ($0 == "name = \"" target "\"") }
  in_target && /^roots = \[/ { collecting = 1; next }
  collecting && /^\]/ { collecting = 0; in_target = 0 }
  collecting { gsub(/[", ]/, ""); if (length($0) > 0) print }
' lakefile.toml)

if [ -z "$roots" ]; then
  echo "FAIL: could not extract roots for lean_lib $TARGET from lakefile.toml" >&2
  exit 1
fi

module_path() { echo "${1//./\/}.lean"; }

# 2. BFS over the static `import` graph, staying inside LeanProofs.*.
declare -A seen
queue=()
for m in $roots; do queue+=("$m"); done

mathlib_offenders=()
heavy_offenders=()
missing=()

while [ ${#queue[@]} -gt 0 ]; do
  mod="${queue[0]}"; queue=("${queue[@]:1}")
  [ -n "${seen[$mod]:-}" ] && continue
  seen[$mod]=1

  for h in "${HEAVY[@]}"; do
    if [ "$mod" = "$h" ]; then heavy_offenders+=("$mod"); fi
  done

  f="$(module_path "$mod")"
  if [ ! -f "$f" ]; then missing+=("$mod -> $f"); continue; fi

  while IFS= read -r imp; do
    case "$imp" in
      Mathlib*) mathlib_offenders+=("$mod imports $imp") ;;
      LeanProofs*) queue+=("$imp") ;;
    esac
  done < <(grep -E '^import ' "$f" | awk '{print $2}')
done

status=0
if [ ${#missing[@]} -gt 0 ]; then
  echo "FAIL: modules in $TARGET closure with no source file:" >&2
  printf '  %s\n' "${missing[@]}" >&2
  status=4
fi
if [ ${#heavy_offenders[@]} -gt 0 ]; then
  echo "FAIL: $TARGET closure reaches AdmissibilityMathlibIslands modules:" >&2
  printf '  %s\n' "${heavy_offenders[@]}" >&2
  status=3
fi
if [ ${#mathlib_offenders[@]} -gt 0 ]; then
  echo "FAIL: $TARGET closure imports Mathlib:" >&2
  printf '  %s\n' "${mathlib_offenders[@]}" >&2
  status=2
fi

if [ "$status" -eq 0 ]; then
  echo "PASS — $TARGET import closure (${#seen[@]} modules) is Mathlib-free and avoids the heavy island"
fi
exit "$status"
