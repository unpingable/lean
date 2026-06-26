#!/usr/bin/env bash
# Check that every LeanProofs/Admissibility/*.lean file carries a
# Custody-Class: marker drawn from the ratified vocabulary.
#
# Ratified classes are defined in:
#   ~/git/papers/working/custody-classes.md
#
# Exit codes:
#   0 — every file has a marker and every marker is a ratified class,
#       and the README's stated counts match the live tally
#   1 — at least one file is missing the marker
#   2 — at least one file declares an unratified class string
#   3 — README prose counts have drifted from the live tally
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

total=$(ls "$ADMISS"/*.lean | wc -l | tr -d ' ')

# 3. README doc-test: stated counts must match the live tally.
# Anchored on the canonical "**CLASS (N)" bullets and the "The N `.lean` files"
# total — NOT on changelog receipts, which deliberately quote historical counts.
# Converts count drift from "someone notices eventually" to a fail-closed gate.
README="$ADMISS/README.md"
if [ -f "$README" ]; then
  doc_fail=0
  for cls in "${RATIFIED[@]}"; do
    stated=$(grep -oE "\*\*${cls} \([0-9]+\)" "$README" | grep -oE '[0-9]+' || true)
    for n in $stated; do
      if [ "$n" -ne "${counts[$cls]}" ]; then
        echo "FAIL: README states $cls = $n but live tally is ${counts[$cls]}" >&2
        doc_fail=1
      fi
    done
  done
  stated_total=$(grep -oE 'The [0-9]+ `\.lean` files' "$README" | grep -oE '[0-9]+' || true)
  for n in $stated_total; do
    if [ "$n" -ne "$total" ]; then
      echo "FAIL: README states $n total .lean files but live count is $total" >&2
      doc_fail=1
    fi
  done
  if [ $doc_fail -ne 0 ]; then
    echo "  (README count drift — reconcile prose against this script's tally)" >&2
    exit 3
  fi
fi

# 4. Report.
echo "OK: $total files; all carry ratified Custody-Class markers; README counts match"
for cls in "${RATIFIED[@]}"; do
  printf "  %-24s %d\n" "$cls" "${counts[$cls]}"
done
