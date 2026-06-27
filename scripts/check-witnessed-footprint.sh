#!/usr/bin/env bash
# Gate 5 — re-attest the Witnessed Derivation Calculus axiom footprint in the
# canonical build context. Fail-closed: every ratified receipt must report EXACTLY
# its documented footprint (RATIFICATION-v1.3.md). This is what prevents future-you
# from quietly turning the Mathlib-free witness library into Mathlib soup, or letting
# a receipt grow a new axiom unnoticed. Exit code is the gate, never eyeballed.
#
# Source of truth for the expected footprints:
#   experiments/no_free_lift_wiring/RATIFICATION-v1.3.md  (with the 2.0 renames applied:
#   WitnessedDerivation->Derivation, Tightened->Discipline, DisciplineObstruction->
#   Obstruction, tightened_metatheory->discipline_metatheory)
#
# Exit codes:
#   0 — Witnessed builds and all 10 receipts are within their attested footprint
#   1 — `lake build Witnessed` failed
#   2 — a receipt drifted (missing/renamed, new axiom, sorry, or wrong footprint)

set -uo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$REPO_ROOT"

P="LeanProofs.Witnessed"
NONE="does not depend on any axioms"
PROPEXT="depends on axioms: [propext]"
PROPEXT_QUOT="depends on axioms: [propext, Quot.sound]"

# Ratified receipt -> expected footprint (EXACT).
declare -A EXPECT=(
  ["$P.Derivation.derivation_extends_along_paid_path"]="$NONE"
  ["$P.Discipline.cut_admissible_general"]="$NONE"
  ["$P.NoFreeLift.paid_lift_sound"]="$NONE"
  ["$P.NoFreeLift.no_free_lift"]="$NONE"
  ["$P.Derivation.revoked_floor_derives_nothing"]="$NONE"
  ["$P.Normalization.bridge_path_normal_form"]="$PROPEXT"
  ["$P.Normalization.bridge_path_two_edge_normal_form"]="$PROPEXT_QUOT"
  ["$P.Obstruction.bridgeValid_discriminating_iff_semanticNontrivial"]="$PROPEXT"
  ["$P.Discipline.embedding_is_witnessed"]="$PROPEXT_QUOT"
  ["$P.Discipline.discipline_metatheory"]="$NONE"
)

# 1. The library must build. The separate `Witnessed` lean_lib is Mathlib-free by
#    construction, so a green build here also proves the isolation held.
if ! lake build Witnessed >/dev/null 2>&1; then
  echo "FAIL: lake build Witnessed did not succeed" >&2
  exit 1
fi

# 2. Probe the footprint via `#print axioms` against the built oleans.
TMP="$(mktemp "${TMPDIR:-/tmp}/witnessed-footprint-XXXXXX.lean")"
trap 'rm -f "$TMP"' EXIT
{
  echo "import LeanProofs.Witnessed"
  for r in "${!EXPECT[@]}"; do echo "#print axioms $r"; done
} > "$TMP"
OUT="$(lake env lean "$TMP" 2>&1)"

# 3. Fail closed on each receipt: exact footprint line must be present.
fail=0
if grep -q 'sorryAx' <<<"$OUT"; then
  echo "FAIL: a receipt depends on sorryAx" >&2
  fail=1
fi
for r in "${!EXPECT[@]}"; do
  if ! grep -Fq "'$r' ${EXPECT[$r]}" <<<"$OUT"; then
    actual="$(grep -F "'$r'" <<<"$OUT")"
    echo "FAIL: $r" >&2
    echo "      expected: ${EXPECT[$r]}" >&2
    echo "      actual:   ${actual:-<no axiom report — renamed or removed?>}" >&2
    fail=1
  fi
done

if [ "$fail" -ne 0 ]; then
  echo "  (footprint drift — reconcile against RATIFICATION-v1.3.md, or the port broke a receipt)" >&2
  exit 2
fi

echo "OK: Witnessed builds Mathlib-free; ${#EXPECT[@]} ratified receipts within attested footprint"
naf=0; pe=0; peq=0
for r in "${!EXPECT[@]}"; do
  case "${EXPECT[$r]}" in
    "$NONE") naf=$((naf+1));;
    "$PROPEXT") pe=$((pe+1));;
    "$PROPEXT_QUOT") peq=$((peq+1));;
  esac
done
echo "    $naf axiom-free, $pe × [propext], $peq × [propext, Quot.sound]"
