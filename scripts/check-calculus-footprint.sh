#!/usr/bin/env bash
# Re-attest the Admissibility.Calculus rung-2 axiom footprint in the
# canonical build context. Fail-closed: every frozen receipt must report
# EXACTLY its documented footprint. This is what prevents the import-free
# governed-family signature (Admissibility Calculus promotion rung 2) from
# quietly growing an axiom, a sorry, an import, or a renamed receipt. Exit
# code is the gate, never eyeballed.
#
# Source of truth for the expected footprints: the rung-2 and rung-3
# candidate packets and hostile reviews of 2026-07-17 (skunkworks
# ADMISSIBILITY_CALCULUS_RUNG2_GOVERNED_FAMILY_CANDIDATE_2026-07-17.md and
# ADMISSIBILITY_CALCULUS_RUNG3_WEATHERING_BOUNDED_PAID_REACHABILITY_
# CANDIDATE_2026-07-17.md), recorded in CLAIM-REGISTER.md entries #20/#21
# and the `#print axioms` receipts in the modules themselves. The frozen
# surface is 22 receipts: the six rung-2 core receipts (all axiom-free)
# plus the sixteen rung-3 instance receipts (ten axiom-free, six exactly
# `[propext]`). `no_claim_erasing_check_is_faithful` is the
# operator-ratified name (renamed from `no_erasing_check_is_faithful`
# before the freeze); `boundedPaidReachability` is the operator-ratified
# bounded family name.
#
# Exit codes:
#   0 — stable root builds; all 22 receipts exact
#   1 — `lake build AdmissibilityCalculus` failed
#   2 — a receipt drifted (missing/renamed, new axiom, sorry, or wrong footprint)

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$REPO_ROOT"

P="Admissibility.Calculus.GovernedFamily"
W="Admissibility.Calculus.Instances.Weathering"
B="Admissibility.Calculus.Instances.BoundedPaidReachability"
NONE="does not depend on any axioms"
PROPEXT="depends on axioms: [propext]"

# Frozen receipt -> expected footprint (EXACT).
declare -A EXPECT=(
  # rung 2 — governed-family core, 6, all axiom-free
  ["$P.refusal_refutes_authority"]="$NONE"
  ["$P.authority_requires_standing"]="$NONE"
  ["$P.authority_preserves_custody"]="$NONE"
  ["$P.authority_has_no_multiplicity"]="$NONE"
  ["$P.authority_iff_decide_isLeft"]="$NONE"
  ["$P.no_claim_erasing_check_is_faithful"]="$NONE"
  # rung 3 — Weathering native, 6, all axiom-free
  ["$W.fresh_may_rely"]="$NONE"
  ["$W.warningBand_may_rely"]="$NONE"
  ["$W.staleness_is_not_negation"]="$NONE"
  ["$W.stale_cannot_rely_directly"]="$NONE"
  ["$W.retired_cannot_rely_directly"]="$NONE"
  ["$W.non_testifying_must_downgrade_reprobe_or_carry"]="$NONE"
  # rung 3 — Weathering governed instance, 3, all axiom-free
  ["$W.weathering_authority_iff_native"]="$NONE"
  ["$W.weathering_refuses_stale_direct"]="$NONE"
  ["$W.stale_direct_has_no_standing"]="$NONE"
  # rung 3 — bounded paid native, 1, exactly [propext]
  ["$B.Staged.Run.occurrence_provenance"]="$PROPEXT"
  # rung 3 — bounded paid governed instance, 6
  ["$B.Barrier.stays"]="$NONE"
  ["$B.authority_iff_lawful_history"]="$PROPEXT"
  ["$B.bare_claim_has_no_standing"]="$PROPEXT"
  ["$B.retro_claim_refused_for_want_of_standing"]="$PROPEXT"
  ["$B.custody_does_not_grant_dynamic_authority"]="$PROPEXT"
  ["$B.signature_refuses_endpoint_only_checks"]="$PROPEXT"
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

echo "OK: AdmissibilityCalculus root builds; all ${#EXPECT[@]} Calculus receipts within their attested footprint"
