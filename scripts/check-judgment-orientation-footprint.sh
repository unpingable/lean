#!/usr/bin/env bash
# Re-attest the JudgmentOrientation axiom footprint in the canonical build
# context. Fail-closed: every frozen receipt must report EXACTLY its
# documented footprint. This is what prevents the Mathlib-free five-module
# family (Core, Attribution, Provenance, OriginSupport, Bridge) from quietly
# growing a new axiom, a sorry, or a renamed receipt. Exit code is the gate,
# never eyeballed.
#
# Source of truth for the expected footprints: the promotion review of
# 2026-07-16 (skunkworks 4f8e076 + in-review Bridge), recorded in
# CLAIM-REGISTER.md entry #18 and the `#print axioms` receipts in
# LeanProofs/JudgmentOrientation.lean. The documented family maximum is
# [propext, Classical.choice, Quot.sound]; the Core confinement laws are
# constructive (no axioms).
#
# Exit codes:
#   0 — stable family and examples annex build; all 13 receipts exact
#   1 — `lake build JudgmentOrientation JudgmentOrientationExamples` failed
#   2 — a receipt drifted (missing/renamed, new axiom, sorry, or wrong footprint)

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$REPO_ROOT"

P="LeanProofs.JudgmentOrientation"
NONE="does not depend on any axioms"
PROPEXT="depends on axioms: [propext]"
PROPEXT_QUOT="depends on axioms: [propext, Quot.sound]"
CLASSICAL_MAX="depends on axioms: [propext, Classical.choice, Quot.sound]"

# Frozen receipt -> expected footprint (EXACT).
declare -A EXPECT=(
  ["$P.OrientationTrace.runRaw_protected"]="$NONE"
  ["$P.no_orientation_without_admission"]="$NONE"
  ["$P.Attribution.change_localizes_to_privileged"]="$CLASSICAL_MAX"
  ["$P.Provenance.duplicate_does_not_raise_heat"]="$PROPEXT"
  ["$P.Provenance.run_replayed_batch_accounting_idempotent"]="$CLASSICAL_MAX"
  ["$P.Provenance.originFaithful_run_decomposed_iff"]="$PROPEXT"
  ["$P.OriginSupport.EffectiveSupport.join_assoc"]="$PROPEXT_QUOT"
  ["$P.OriginSupport.EffectiveSupport.join_le_iff"]="$PROPEXT_QUOT"
  ["$P.OriginSupport.EffectiveSupport.ofTrace_append"]="$PROPEXT_QUOT"
  ["$P.OriginSupport.EffectiveSupport.ofState_run"]="$PROPEXT_QUOT"
  ["$P.OriginSupport.EffectiveSupport.replayed_custody_strictly_grows"]="$PROPEXT"
  ["$P.Bridge.changed_protected_has_supported_privileged_origin"]="$CLASSICAL_MAX"
  ["$P.Bridge.certification_change_has_supported_privileged_origin"]="$CLASSICAL_MAX"
)

# 1. The stable family and the examples annex must build. Both libs are
#    Mathlib-free by construction, so a green build also proves isolation held.
if ! lake build JudgmentOrientation JudgmentOrientationExamples >/dev/null 2>&1; then
  echo "FAIL: lake build JudgmentOrientation JudgmentOrientationExamples did not succeed" >&2
  exit 1
fi

# 2. Probe the footprint via `#print axioms` against the built oleans.
TMP="$(mktemp "${TMPDIR:-/tmp}/judgment-orientation-footprint-XXXXXX.lean")"
trap 'rm -f "$TMP"' EXIT
{
  echo "import LeanProofs.JudgmentOrientation"
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

echo "OK: JudgmentOrientation family builds; all ${#EXPECT[@]} receipts within their attested footprint"
