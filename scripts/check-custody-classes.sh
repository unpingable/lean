#!/usr/bin/env bash
# Check that every LeanProofs/Admissibility/*.lean file carries a
# Custody-Class: marker drawn from the ratified vocabulary.
#
# Ratified classes are defined in:
#   ~/git/papers/working/custody-classes.md
#
# Exit codes:
#   0 — every file has a marker and every marker is a ratified class
#   1 — at least one file is missing the marker
#   2 — at least one file declares an unratified class string
#
# This is the Phase 3 grep-target promise made executable.

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
ADMISS="$REPO_ROOT/LeanProofs/Admissibility"

RATIFIED=( PUBLIC-SHIPPED ANNEX SCRATCH UNRATIFIED-CANDIDATE DEPRECATED )

# 1. Missing-marker check.
missing=$(grep -L "Custody-Class:" "$ADMISS"/*.lean || true)
if [ -n "$missing" ]; then
  echo "FAIL: files missing Custody-Class: marker:" >&2
  echo "$missing" >&2
  exit 1
fi

# 2. Unratified-string check.
fail=0
declare -A counts
for cls in "${RATIFIED[@]}"; do counts[$cls]=0; done

for f in "$ADMISS"/*.lean; do
  decl=$(grep -m1 -E "^\s*Custody-Class:\s*" "$f" | sed -E 's/^\s*Custody-Class:\s*//; s/\s+$//')
  ratified=0
  for cls in "${RATIFIED[@]}"; do
    if [ "$decl" = "$cls" ]; then ratified=1; counts[$cls]=$((counts[$cls]+1)); break; fi
  done
  if [ $ratified -eq 0 ]; then
    echo "FAIL: $f declares unratified class: '$decl'" >&2
    fail=1
  fi
done
if [ $fail -ne 0 ]; then exit 2; fi

# 3. Report.
echo "OK: $(ls "$ADMISS"/*.lean | wc -l) files; all carry ratified Custody-Class markers"
for cls in "${RATIFIED[@]}"; do
  printf "  %-24s %d\n" "$cls" "${counts[$cls]}"
done
