#!/usr/bin/env bash
# Re-attest the Admissibility.Calculus rung-2 axiom footprint in the
# canonical build context. Fail-closed: every frozen receipt must report
# EXACTLY its documented footprint. This is what prevents the import-free
# governed-family signature (Admissibility Calculus promotion rung 2) from
# quietly growing an axiom, a sorry, an import, or a renamed receipt. Exit
# code is the gate, never eyeballed.
#
# Source of truth for the expected footprints: the rung-2 candidate packet
# and hostile review of 2026-07-17 (skunkworks
# ADMISSIBILITY_CALCULUS_RUNG2_GOVERNED_FAMILY_CANDIDATE_2026-07-17.md),
# recorded in CLAIM-REGISTER.md entry #20 and the `#print axioms` receipts
# in the module itself. The frozen surface is one structure, one derived
# definition, and six theorems — all six axiom-free.
# `no_claim_erasing_check_is_faithful` is the operator-ratified name
# (renamed from `no_erasing_check_is_faithful` before the freeze).
#
# Exit codes:
#   0 — stable root builds; all 6 receipts exact
#   1 — `lake build AdmissibilityCalculus` failed
#   2 — a receipt drifted (missing/renamed, new axiom, sorry, or wrong footprint)

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$REPO_ROOT"

P="Admissibility.Calculus.GovernedFamily"
NONE="does not depend on any axioms"

# Frozen receipt -> expected footprint (EXACT).
declare -A EXPECT=(
  ["$P.refusal_refutes_authority"]="$NONE"
  ["$P.authority_requires_standing"]="$NONE"
  ["$P.authority_preserves_custody"]="$NONE"
  ["$P.authority_has_no_multiplicity"]="$NONE"
  ["$P.authority_iff_decide_isLeft"]="$NONE"
  ["$P.no_claim_erasing_check_is_faithful"]="$NONE"
)

# 1. The stable root must build. The lib is import-free below Lean core and
#    Mathlib-free by construction, so a green build also proves isolation.
if ! lake build AdmissibilityCalculus >/dev/null 2>&1; then
  echo "FAIL: lake build AdmissibilityCalculus did not succeed" >&2
  exit 1
fi

# 2. Probe the footprint via `#print axioms` against the built oleans.
TMP="$(mktemp "${TMPDIR:-/tmp}/calculus-footprint-XXXXXX.lean")"
trap 'rm -f "$TMP"' EXIT
{
  echo "import LeanProofs.Admissibility.Calculus"
  for receipt in "${!EXPECT[@]}"; do echo "#print axioms $receipt"; done
} > "$TMP"
if ! OUT="$(lake env lean "$TMP" 2>&1)"; then
  echo "$OUT" >&2
  echo "FAIL: footprint probe (lake env lean) did not succeed — a receipt is likely renamed/removed" >&2
  exit 2
fi

# 3. Normalize: `#print axioms` wraps long axiom lists across lines; join each
#    receipt's report onto one line and squeeze whitespace before comparing.
NORMALIZED="$(printf '%s\n' "$OUT" | awk "
  /^'/ { if (buf != \"\") print buf; buf = \$0; next }
  { buf = buf \" \" \$0 }
  END { if (buf != \"\") print buf }
" | tr -s ' ')"

fail=0
for receipt in "${!EXPECT[@]}"; do
  line="$(printf '%s\n' "$NORMALIZED" | grep -F "'$receipt'" || true)"
  if [ -z "$line" ]; then
    echo "FAIL: missing or renamed receipt: $receipt" >&2
    fail=1
    continue
  fi
  want="'$receipt' ${EXPECT[$receipt]}"
  if [ "$line" != "$want" ]; then
    echo "FAIL: footprint drift on $receipt" >&2
    echo "   got: $line" >&2
    echo "  want: $want" >&2
    fail=1
  fi
done

if [ "$fail" -ne 0 ]; then exit 2; fi

echo "OK: AdmissibilityCalculus root builds; all ${#EXPECT[@]} rung-2 receipts within their attested footprint"
