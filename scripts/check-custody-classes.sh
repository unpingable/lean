#!/usr/bin/env bash
# Check the registered custody surfaces:
#   * every LeanProofs/Admissibility/*.lean file carries a ratified marker;
#   * the eight-module PaidRecomposition stable closure and three fenced
#     evidence modules carry their exact release classifications.
#   * the JudgmentOrientation stable root/core and examples annex carry their
#     exact promotion classifications.
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
#   4 — the PaidRecomposition registry is missing, unexpected, or misclassified
#   5 — the JudgmentOrientation registry is missing, unexpected, or misclassified
#
# This is the Phase 3 grep-target promise made executable.

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
ADMISS="$REPO_ROOT/LeanProofs/Admissibility"
PAID_ROOT="$REPO_ROOT/LeanProofs/Witnessed/PaidRecomposition.lean"
PAID_DIR="$REPO_ROOT/LeanProofs/Witnessed/PaidRecomposition"
NO_FREE_LIFT="$REPO_ROOT/LeanProofs/Witnessed/NoFreeLift.lean"
DERIVATION="$REPO_ROOT/LeanProofs/Witnessed/Derivation.lean"
SEQUENT="$REPO_ROOT/LeanProofs/Witnessed/Sequent.lean"
RESOURCE_SEQUENT="$REPO_ROOT/LeanProofs/Witnessed/ResourceSequent.lean"
RESOURCE_CHECKER="$REPO_ROOT/LeanProofs/Witnessed/ResourceChecker.lean"
ORIENTATION_ROOT="$REPO_ROOT/LeanProofs/JudgmentOrientation.lean"
ORIENTATION_DIR="$REPO_ROOT/LeanProofs/JudgmentOrientation"

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

# 4. Exact PaidRecomposition custody registry. This is intentionally
# fail-closed: adding a new stable or evidence module requires an explicit
# custody decision here rather than inheriting one from its directory name.
declare -A paid_expected=(
  ["$PAID_ROOT"]="PUBLIC-SHIPPED"
  ["$PAID_DIR/Payment.lean"]="PUBLIC-SHIPPED"
  ["$PAID_DIR/Catalog.lean"]="PUBLIC-SHIPPED"
  ["$RESOURCE_CHECKER"]="PUBLIC-SHIPPED"
  ["$RESOURCE_SEQUENT"]="PUBLIC-SHIPPED"
  ["$SEQUENT"]="PUBLIC-SHIPPED"
  ["$DERIVATION"]="PUBLIC-SHIPPED"
  ["$NO_FREE_LIFT"]="PUBLIC-SHIPPED"
  ["$PAID_DIR/Applications/ResourceTraceOneCrossing.lean"]="ANNEX"
  ["$PAID_DIR/Countermodels/EndpointCompleteness.lean"]="ANNEX"
  ["$PAID_DIR/Applications/FiniteSupportOneCrossing.lean"]="ANNEX"
)

paid_fail=0
for f in "${!paid_expected[@]}"; do
  if [ ! -f "$f" ]; then
    echo "FAIL: registered PaidRecomposition source is missing: $f" >&2
    paid_fail=1
    continue
  fi
  marker_count=$(sed -n '1,40p' "$f" |
    grep -cE '^[[:space:]]*Custody-Class:[[:space:]]*' || true)
  declared=$(sed -n '1,40p' "$f" |
    grep -m1 -E '^[[:space:]]*Custody-Class:[[:space:]]*' |
    sed -E 's/^[[:space:]]*Custody-Class:[[:space:]]*//; s/[[:space:]]+$//' || true)
  if [ "$marker_count" -ne 1 ] || [ "$declared" != "${paid_expected[$f]}" ]; then
    echo "FAIL: $f custody is '${declared:-<missing>}'" >&2
    echo "      expected: ${paid_expected[$f]}" >&2
    paid_fail=1
  fi
done

mapfile -t paid_actual < <(
  {
    [ -f "$PAID_ROOT" ] && printf '%s\n' "$PAID_ROOT"
    find "$PAID_DIR" -type f -name '*.lean' -print 2>/dev/null
  } | sort
)
for f in "${paid_actual[@]}"; do
  if [ -z "${paid_expected[$f]+registered}" ]; then
    echo "FAIL: unregistered PaidRecomposition source has no custody decision: $f" >&2
    paid_fail=1
  fi
done

if [ "$paid_fail" -ne 0 ]; then exit 4; fi

# 5. Exact JudgmentOrientation custody registry. The stable root imports only
# the five theorem modules; examples remain a separately imported ANNEX.
declare -A orientation_expected=(
  ["$ORIENTATION_ROOT"]="PUBLIC-SHIPPED"
  ["$ORIENTATION_DIR/Core.lean"]="PUBLIC-SHIPPED"
  ["$ORIENTATION_DIR/Attribution.lean"]="PUBLIC-SHIPPED"
  ["$ORIENTATION_DIR/Provenance.lean"]="PUBLIC-SHIPPED"
  ["$ORIENTATION_DIR/OriginSupport.lean"]="PUBLIC-SHIPPED"
  ["$ORIENTATION_DIR/Bridge.lean"]="PUBLIC-SHIPPED"
  ["$ORIENTATION_DIR/Examples.lean"]="ANNEX"
)

orientation_fail=0
for f in "${!orientation_expected[@]}"; do
  if [ ! -f "$f" ]; then
    echo "FAIL: registered JudgmentOrientation source is missing: $f" >&2
    orientation_fail=1
    continue
  fi
  marker_count=$(sed -n '1,40p' "$f" |
    grep -cE '^[[:space:]]*Custody-Class:[[:space:]]*' || true)
  declared=$(sed -n '1,40p' "$f" |
    grep -m1 -E '^[[:space:]]*Custody-Class:[[:space:]]*' |
    sed -E 's/^[[:space:]]*Custody-Class:[[:space:]]*//; s/[[:space:]]+$//' || true)
  if [ "$marker_count" -ne 1 ] || [ "$declared" != "${orientation_expected[$f]}" ]; then
    echo "FAIL: $f custody is '${declared:-<missing>}'" >&2
    echo "      expected: ${orientation_expected[$f]}" >&2
    orientation_fail=1
  fi
done

mapfile -t orientation_actual < <(
  {
    [ -f "$ORIENTATION_ROOT" ] && printf '%s\n' "$ORIENTATION_ROOT"
    find "$ORIENTATION_DIR" -type f -name '*.lean' -print 2>/dev/null
  } | sort
)
for f in "${orientation_actual[@]}"; do
  if [ -z "${orientation_expected[$f]+registered}" ]; then
    echo "FAIL: unregistered JudgmentOrientation source has no custody decision: $f" >&2
    orientation_fail=1
  fi
done

# Import custody is exact as well: the stable root cannot silently absorb the
# examples annex, and no theorem module can acquire a Scratch/Mathlib edge.
declare -A orientation_imports_expected=(
  ["$ORIENTATION_ROOT"]="LeanProofs.JudgmentOrientation.Core LeanProofs.JudgmentOrientation.Attribution LeanProofs.JudgmentOrientation.Provenance LeanProofs.JudgmentOrientation.OriginSupport LeanProofs.JudgmentOrientation.Bridge"
  ["$ORIENTATION_DIR/Core.lean"]=""
  ["$ORIENTATION_DIR/Attribution.lean"]="LeanProofs.JudgmentOrientation.Core"
  ["$ORIENTATION_DIR/Provenance.lean"]=""
  ["$ORIENTATION_DIR/OriginSupport.lean"]="LeanProofs.JudgmentOrientation.Provenance"
  ["$ORIENTATION_DIR/Bridge.lean"]="LeanProofs.JudgmentOrientation.Core LeanProofs.JudgmentOrientation.Attribution LeanProofs.JudgmentOrientation.Provenance LeanProofs.JudgmentOrientation.OriginSupport"
  ["$ORIENTATION_DIR/Examples.lean"]="LeanProofs.JudgmentOrientation.Core LeanProofs.JudgmentOrientation.Attribution LeanProofs.JudgmentOrientation.Provenance LeanProofs.JudgmentOrientation.OriginSupport LeanProofs.JudgmentOrientation.Bridge"
)

for f in "${!orientation_imports_expected[@]}"; do
  actual_imports=$({ grep -E '^import ' "$f" || true; } |
    awk '{print $2}' | paste -sd ' ' -)
  if [ "$actual_imports" != "${orientation_imports_expected[$f]}" ]; then
    echo "FAIL: $f imports '$actual_imports'" >&2
    echo "      expected: '${orientation_imports_expected[$f]}'" >&2
    orientation_fail=1
  fi
done

if [ "$orientation_fail" -ne 0 ]; then exit 5; fi

# 6. Report.
echo "OK: $total files; all carry ratified Custody-Class markers; README counts match"
for cls in "${RATIFIED[@]}"; do
  printf "  %-24s %d\n" "$cls" "${counts[$cls]}"
done
echo "OK: ${#paid_expected[@]} PaidRecomposition files match the exact custody registry"
echo "  PUBLIC-SHIPPED           8 (exact stable import closure)"
echo "  ANNEX                    3 (one imports an explicit SCRATCH dependency)"
echo "OK: ${#orientation_expected[@]} JudgmentOrientation files match the exact custody registry"
echo "  PUBLIC-SHIPPED           6"
echo "  ANNEX                    1 (examples; excluded from the stable root)"
