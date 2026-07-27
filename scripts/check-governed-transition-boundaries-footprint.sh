#!/usr/bin/env bash
# V16 candidate signature and exact axiom-footprint replay.

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$REPO_ROOT"

if ! lake build GovernedTransitionBoundaries \
    GovernedTransitionBoundariesEvidence >/dev/null 2>&1; then
  echo "FAIL: governed-transition-boundaries targets did not build" >&2
  exit 1
fi

P="LeanProofs.GovernedTransitionBoundaries"
E="LeanProofs.GovernedTransitionBoundariesEvidence"
NONE="does not depend on any axioms"
PROPEXT="depends on axioms: [propext]"
PROPEXT_QUOT="depends on axioms: [propext, Quot.sound]"

declare -A EXPECT=(
  ["$P.explicitFactorization_compose"]="$NONE"
  ["$P.explicitFactorization_implies_determines"]="$NONE"
  ["$P.target_collision_blocks_explicit_factorization"]="$NONE"
  ["$P.derived_view_cannot_restore_target"]="$NONE"
  ["$E.declared_analysis_atlas_has_1024_cases"]="$NONE"
  ["$E.declared_analysis_atlas_covers"]="$PROPEXT_QUOT"
  ["$E.declared_coordinate_language_has_128_selections"]="$NONE"
  ["$E.declared_coordinate_language_covers"]="$PROPEXT"
  ["$E.declared_coordinate_language_has_no_duplicates"]="$NONE"
  ["$E.selected_internal_target_factors_through_internal_carrier"]="$PROPEXT"
  ["$E.selected_internal_exact_iff_includes_declared_minimum"]="$PROPEXT_QUOT"
  ["$E.selected_internal_declared_minimum_is_least"]="$PROPEXT_QUOT"
  ["$E.selected_internal_declared_least_is_unique"]="$PROPEXT_QUOT"
  ["$E.selected_internal_mask_membership_iff_exact"]="$PROPEXT_QUOT"
  ["$E.selected_internal_exact_mask_count"]="$NONE"
  ["$E.selected_internal_exact_masks_have_no_duplicates"]="$NONE"
  ["$E.selected_internal_exact_mask_classification"]="$PROPEXT_QUOT"
  ["$E.no_declared_selection_is_exact_for_modeled_grounding"]="$PROPEXT"
  ["$E.no_declared_selection_is_exact_for_six_target"]="$PROPEXT"
  ["$E.all_admitted_coordinates_five_target_boundary"]="$PROPEXT"
  ["$E.all_admitted_coordinates_do_not_factor_six_target"]="$PROPEXT"
  ["$E.computationally_sufficient_product_can_be_refused"]="$PROPEXT"
  ["$E.issued_observation_record_does_not_factor_later_validity"]="$NONE"
  ["$E.issued_observation_derivative_does_not_restore_later_validity"]="$NONE"
  ["$E.exact_current_pair_certificates_do_not_instantiate_selected_triple"]="$NONE"
  ["$E.present_state_does_not_factor_occurrence_link"]="$NONE"
  ["$E.present_state_derivative_does_not_restore_occurrence_link"]="$NONE"
  ["$E.admitted_acquisition_interface_does_not_factor_modeled_relation"]="$NONE"
  ["$E.admitted_interface_derivative_does_not_restore_modeled_relation"]="$NONE"
)

TMP="$(mktemp "${TMPDIR:-/tmp}/governed-transition-boundaries-footprint-XXXXXX.lean")"
trap 'rm -f "$TMP"' EXIT
{
  echo "import LeanProofs.GovernedTransitionBoundariesEvidence"
  for receipt in "${!EXPECT[@]}"; do
    echo "#print axioms $receipt"
  done
} > "$TMP"

if ! OUT="$(lake env lean "$TMP" 2>&1)"; then
  echo "$OUT" >&2
  echo "FAIL: governed-transition-boundaries footprint probe did not compile" >&2
  exit 2
fi

NORMALIZED="$(printf '%s\n' "$OUT" | awk "
  /^'/ { if (buf != \"\") print buf; buf = \$0; next }
  { buf = buf \" \" \$0 }
  END { if (buf != \"\") print buf }
" | tr -s ' ')"

fail=0
for receipt in "${!EXPECT[@]}"; do
  line="$(printf '%s\n' "$NORMALIZED" | grep -F "'$receipt'" || true)"
  want="'$receipt' ${EXPECT[$receipt]}"
  if [ "$line" != "$want" ]; then
    echo "FAIL: footprint drift on $receipt" >&2
    echo "   got: ${line:-<missing>}" >&2
    echo "  want: $want" >&2
    fail=1
  fi
done

if grep -q "sorryAx\\|Classical.choice" <<<"$NORMALIZED"; then
  echo "FAIL: prohibited footprint dependency detected" >&2
  fail=1
fi

if [ "$fail" -ne 0 ]; then
  exit 3
fi

echo "PASS — all ${#EXPECT[@]} governed-transition-boundaries theorem footprints replay exactly"
