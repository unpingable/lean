#!/usr/bin/env bash
# Post-v11 gate for the corrected stable PaidRecomposition import closure.
#
# This gate fails closed over custody, the stable import boundary, the frozen
# public API names, exact theorem axiom footprints, and the Mathlib/SCRATCH-free
# import closure. The unchanged checker/WDC foundation is public shipped
# substrate because the stable Payment surface already imports it. Applications
# and countermodels remain registered ANNEX evidence outside the stable root and
# `Witnessed` build target.
#
# Exit codes:
#   0 — all source, graph, build, API, and footprint checks pass
#   1 — a source is missing or has the wrong exact custody marker
#   2 — root/wiring/build ownership or stable import isolation drifted
#   3 — a placeholder/hole was found or the stable target did not build
#   4 — the frozen API/footprint probe did not elaborate
#   5 — a theorem's exact classified axiom footprint drifted

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$REPO_ROOT"

P="LeanProofs.Witnessed.PaidRecomposition"
ROOT_MODULE="$P"
PAYMENT_MODULE="$P.Payment"
CATALOG_MODULE="$P.Catalog"
ROOT_FILE="LeanProofs/Witnessed/PaidRecomposition.lean"
PAYMENT_FILE="LeanProofs/Witnessed/PaidRecomposition/Payment.lean"
CATALOG_FILE="LeanProofs/Witnessed/PaidRecomposition/Catalog.lean"
RESOURCE_CHECKER_MODULE="LeanProofs.Witnessed.ResourceChecker"
RESOURCE_SEQUENT_MODULE="LeanProofs.Witnessed.ResourceSequent"
SEQUENT_MODULE="LeanProofs.Witnessed.Sequent"
DERIVATION_MODULE="LeanProofs.Witnessed.Derivation"
NO_FREE_LIFT_MODULE="LeanProofs.Witnessed.NoFreeLift"
RESOURCE_CHECKER_FILE="LeanProofs/Witnessed/ResourceChecker.lean"
RESOURCE_SEQUENT_FILE="LeanProofs/Witnessed/ResourceSequent.lean"
SEQUENT_FILE="LeanProofs/Witnessed/Sequent.lean"
DERIVATION_FILE="LeanProofs/Witnessed/Derivation.lean"
NO_FREE_LIFT_FILE="LeanProofs/Witnessed/NoFreeLift.lean"
PUBLIC_APP_FILE="LeanProofs/Witnessed/PaidRecomposition/Applications/ResourceTraceOneCrossing.lean"
COUNTERMODEL_FILE="LeanProofs/Witnessed/PaidRecomposition/Countermodels/EndpointCompleteness.lean"
FINITE_SUPPORT_FILE="LeanProofs/Witnessed/PaidRecomposition/Applications/FiniteSupportOneCrossing.lean"

declare -A EXPECTED_CUSTODY=(
  ["$ROOT_FILE"]="PUBLIC-SHIPPED"
  ["$PAYMENT_FILE"]="PUBLIC-SHIPPED"
  ["$CATALOG_FILE"]="PUBLIC-SHIPPED"
  ["$RESOURCE_CHECKER_FILE"]="PUBLIC-SHIPPED"
  ["$RESOURCE_SEQUENT_FILE"]="PUBLIC-SHIPPED"
  ["$SEQUENT_FILE"]="PUBLIC-SHIPPED"
  ["$DERIVATION_FILE"]="PUBLIC-SHIPPED"
  ["$NO_FREE_LIFT_FILE"]="PUBLIC-SHIPPED"
  ["$PUBLIC_APP_FILE"]="ANNEX"
  ["$COUNTERMODEL_FILE"]="ANNEX"
  ["$FINITE_SUPPORT_FILE"]="ANNEX"
)
ALL_FILES=(
  "$ROOT_FILE"
  "$PAYMENT_FILE"
  "$CATALOG_FILE"
  "$RESOURCE_CHECKER_FILE"
  "$RESOURCE_SEQUENT_FILE"
  "$SEQUENT_FILE"
  "$DERIVATION_FILE"
  "$NO_FREE_LIFT_FILE"
  "$PUBLIC_APP_FILE"
  "$COUNTERMODEL_FILE"
  "$FINITE_SUPPORT_FILE"
)

# Exact source custody, including fenced evidence.
for file in "${ALL_FILES[@]}"; do
  if [ ! -f "$file" ]; then
    echo "FAIL: missing registered PaidRecomposition source: $file" >&2
    exit 1
  fi
  total_marker_count="$(sed -n '1,40p' "$file" |
    grep -cE '^[[:space:]]*Custody-Class:[[:space:]]*' || true)"
  marker_count="$(sed -n '1,40p' "$file" |
    grep -cE "^[[:space:]]*Custody-Class:[[:space:]]*${EXPECTED_CUSTODY[$file]}[[:space:]]*$" || true)"
  if [ "$total_marker_count" -ne 1 ] || [ "$marker_count" -ne 1 ]; then
    echo "FAIL: $file must carry exactly one header marker:" >&2
    echo "      Custody-Class: ${EXPECTED_CUSTODY[$file]}" >&2
    exit 1
  fi
done

# Parse every module token on an import command and ignore the trailing line
# comment. This parser is shared by the exact graph and direct-SCRATCH checks so
# a second module on the same import line cannot evade either boundary.
direct_imports() {
  awk '
  /^[[:space:]]*import[[:space:]]/ {
    for (i = 2; i <= NF; i++) {
      if ($i ~ /^--/) break
      print $i
    }
  }
  ' "$1"
}

SCRATCH_FREE_FILES=(
  "$ROOT_FILE"
  "$PAYMENT_FILE"
  "$CATALOG_FILE"
  "$RESOURCE_CHECKER_FILE"
  "$RESOURCE_SEQUENT_FILE"
  "$SEQUENT_FILE"
  "$DERIVATION_FILE"
  "$NO_FREE_LIFT_FILE"
  "$PUBLIC_APP_FILE"
  "$COUNTERMODEL_FILE"
)
for file in "${SCRATCH_FREE_FILES[@]}"; do
  mapfile -t forbidden_direct < <(
    direct_imports "$file" | grep -E '^(LeanProofs\.Scratch|Mathlib)' || true
  )
  if [ "${#forbidden_direct[@]}" -ne 0 ]; then
    echo "FAIL: $file has a forbidden direct SCRATCH/Mathlib import" >&2
    printf '  %s\n' "${forbidden_direct[@]}" >&2
    exit 1
  fi
done

mapfile -t finite_support_scratch_imports < <(
  direct_imports "$FINITE_SUPPORT_FILE" | grep -E '^LeanProofs\.Scratch' || true
)
if [ "${#finite_support_scratch_imports[@]}" -ne 1 ] ||
   [ "${finite_support_scratch_imports[0]:-}" != "LeanProofs.Scratch.FiniteSupportChecker" ]; then
  echo "FAIL: finite-support ANNEX direct SCRATCH import set must be exactly:" >&2
  echo "      LeanProofs.Scratch.FiniteSupportChecker" >&2
  printf '  actual: %s\n' "${finite_support_scratch_imports[*]:-<none>}" >&2
  exit 1
fi

# Freeze the exact direct-import graph of all eight stable closure modules.
declare -A EXPECTED_STABLE_IMPORTS=(
  ["$ROOT_FILE"]="$PAYMENT_MODULE $CATALOG_MODULE"
  ["$PAYMENT_FILE"]="$RESOURCE_CHECKER_MODULE"
  ["$CATALOG_FILE"]="$PAYMENT_MODULE"
  ["$RESOURCE_CHECKER_FILE"]="$RESOURCE_SEQUENT_MODULE"
  ["$RESOURCE_SEQUENT_FILE"]="$SEQUENT_MODULE"
  ["$SEQUENT_FILE"]="$DERIVATION_MODULE"
  ["$DERIVATION_FILE"]="$NO_FREE_LIFT_MODULE"
  ["$NO_FREE_LIFT_FILE"]=""
)
for file in "${!EXPECTED_STABLE_IMPORTS[@]}"; do
  actual_imports="$(direct_imports "$file" | paste -sd ' ' -)"
  if [ "$actual_imports" != "${EXPECTED_STABLE_IMPORTS[$file]}" ]; then
    echo "FAIL: stable PaidRecomposition closure import graph drifted at $file" >&2
    echo "      expected: '${EXPECTED_STABLE_IMPORTS[$file]}'" >&2
    echo "      actual:   '$actual_imports'" >&2
    exit 2
  fi
done

if [ "$(grep -cE '^[[:space:]]*import[[:space:]]+LeanProofs\.Witnessed\.PaidRecomposition([[:space:]]|$)' LeanProofs/Witnessed.lean || true)" -ne 1 ]; then
  echo "FAIL: LeanProofs.Witnessed must import the stable PaidRecomposition root exactly once" >&2
  exit 2
fi

# The Witnessed library must use exact module ownership, not a recursive glob
# that silently compiles evidence. Evidence names belong only to their separate,
# non-default PaidRecompositionEvidence library.
witnessed_block="$(awk '
  /^\[\[lean_lib\]\]$/ {
    if (capture) exit
    in_lib = 1
    next
  }
  in_lib && /^name = "Witnessed"$/ { capture = 1 }
  capture { print }
' lakefile.toml)"
if [ -z "$witnessed_block" ]; then
  echo "FAIL: missing Witnessed lean_lib configuration" >&2
  exit 2
fi
if grep -Eq 'Witnessed\.\+|Applications|Countermodels|FiniteSupportOneCrossing' <<<"$witnessed_block"; then
  echo "FAIL: Witnessed build ownership reaches recursive/evidence modules" >&2
  echo "$witnessed_block" >&2
  exit 2
fi
for module in \
  "$ROOT_MODULE" \
  "$PAYMENT_MODULE" \
  "$CATALOG_MODULE" \
  "$RESOURCE_CHECKER_MODULE" \
  "$RESOURCE_SEQUENT_MODULE" \
  "$SEQUENT_MODULE" \
  "$DERIVATION_MODULE" \
  "$NO_FREE_LIFT_MODULE"; do
  if ! grep -Fq "\"$module\"" <<<"$witnessed_block"; then
    echo "FAIL: Witnessed build ownership omits stable module $module" >&2
    exit 2
  fi
done

evidence_block="$(awk '
  /^\[\[lean_lib\]\]$/ {
    if (capture) exit
    in_lib = 1
    next
  }
  in_lib && /^name = "PaidRecompositionEvidence"$/ { capture = 1 }
  capture { print }
' lakefile.toml)"
for module in \
  "$P.Applications.ResourceTraceOneCrossing" \
  "$P.Countermodels.EndpointCompleteness" \
  "$P.Applications.FiniteSupportOneCrossing"; do
  if ! grep -Fq "\"$module\"" <<<"$evidence_block"; then
    echo "FAIL: focused evidence ownership omits $module" >&2
    exit 2
  fi
done

default_targets="$(awk '
  /^defaultTargets[[:space:]]*=/ { capture = 1 }
  capture { print }
  capture && /\]/ { exit }
' lakefile.toml)"
if grep -Fq 'PaidRecompositionEvidence' <<<"$default_targets"; then
  echo "FAIL: PaidRecompositionEvidence must remain outside defaultTargets" >&2
  exit 2
fi

# Reject source holes and explicit placeholder markers throughout the stable and
# evidence modules. The receipt probe independently rejects transitive sorryAx.
hole_hits="$(grep -nEi \
  '(^|[^[:alnum:]_])(sorry|admit|by\?|TODO|FIXME|PLACEHOLDER)([^[:alnum:]_]|$)' \
  "${ALL_FILES[@]}" 2>/dev/null || true)"
if [ -n "$hole_hits" ]; then
  echo "FAIL: PaidRecomposition source contains a hole/placeholder marker:" >&2
  echo "$hole_hits" >&2
  exit 3
fi

# Walk the local stable-root import closure. Missing LeanProofs sources fail
# closed. Mathlib, SCRATCH, and evidence custody are forbidden transitively.
module_path() { echo "${1//./\/}.lean"; }

declare -A seen=()
queue=("$ROOT_MODULE")
mathlib_offenders=()
scratch_offenders=()
evidence_offenders=()
missing_sources=()

while [ "${#queue[@]}" -gt 0 ]; do
  module="${queue[0]}"
  queue=("${queue[@]:1}")
  [ -n "${seen[$module]:-}" ] && continue
  seen["$module"]=1

  file="$(module_path "$module")"
  if [ ! -f "$file" ]; then
    missing_sources+=("$module -> $file")
    continue
  fi

  case "$module" in
    LeanProofs.Scratch*) scratch_offenders+=("$module") ;;
    *.Applications.*|*.Countermodels.*) evidence_offenders+=("$module") ;;
  esac

  while IFS= read -r imported; do
    case "$imported" in
      Mathlib*) mathlib_offenders+=("$module imports $imported") ;;
      LeanProofs.Scratch*) scratch_offenders+=("$module imports $imported") ;;
      LeanProofs.Witnessed.PaidRecomposition.Applications.*|LeanProofs.Witnessed.PaidRecomposition.Countermodels.*)
        evidence_offenders+=("$module imports $imported") ;;
      LeanProofs*) queue+=("$imported") ;;
    esac
  done < <(direct_imports "$file")
done

if [ "${#missing_sources[@]}" -gt 0 ] ||
   [ "${#mathlib_offenders[@]}" -gt 0 ] ||
   [ "${#scratch_offenders[@]}" -gt 0 ] ||
   [ "${#evidence_offenders[@]}" -gt 0 ]; then
  echo "FAIL: stable PaidRecomposition import isolation drifted" >&2
  printf '  missing:  %s\n' "${missing_sources[@]:-}" >&2
  printf '  Mathlib:  %s\n' "${mathlib_offenders[@]:-}" >&2
  printf '  SCRATCH:  %s\n' "${scratch_offenders[@]:-}" >&2
  printf '  evidence: %s\n' "${evidence_offenders[@]:-}" >&2
  exit 2
fi

declare -A EXPECTED_STABLE_MODULES=(
  ["$ROOT_MODULE"]=1
  ["$PAYMENT_MODULE"]=1
  ["$CATALOG_MODULE"]=1
  ["$RESOURCE_CHECKER_MODULE"]=1
  ["$RESOURCE_SEQUENT_MODULE"]=1
  ["$SEQUENT_MODULE"]=1
  ["$DERIVATION_MODULE"]=1
  ["$NO_FREE_LIFT_MODULE"]=1
)
closure_fail=0
for module in "${!seen[@]}"; do
  if [ -z "${EXPECTED_STABLE_MODULES[$module]+expected}" ]; then
    echo "FAIL: unexpected module in stable PaidRecomposition closure: $module" >&2
    closure_fail=1
  fi
done
for module in "${!EXPECTED_STABLE_MODULES[@]}"; do
  if [ -z "${seen[$module]+present}" ]; then
    echo "FAIL: expected stable PaidRecomposition closure module is absent: $module" >&2
    closure_fail=1
  fi
done
if [ "${#seen[@]}" -ne "${#EXPECTED_STABLE_MODULES[@]}" ]; then
  echo "FAIL: stable PaidRecomposition closure must contain exactly eight modules" >&2
  echo "      actual count: ${#seen[@]}" >&2
  closure_fail=1
fi
if [ "$closure_fail" -ne 0 ]; then exit 2; fi

if ! lake build Witnessed "$ROOT_MODULE" PaidRecompositionEvidence >/dev/null 2>&1; then
  echo "FAIL: stable Witnessed/PaidRecomposition or fenced evidence build did not succeed" >&2
  exit 3
fi

NONE="does not depend on any axioms"
PROPEXT="depends on axioms: [propext]"
PROPEXT_QUOT="depends on axioms: [propext, Quot.sound]"
NF="LeanProofs.Witnessed.NoFreeLift"
D="LeanProofs.Witnessed.Derivation"
S="LeanProofs.Witnessed.Sequent"
RS="LeanProofs.Witnessed.ResourceSequent"
RC="LeanProofs.Witnessed.ResourceChecker"

# Exact canonical-toolchain baseline. The non-empty payment reports arise from
# Core list/proposition normalization used by `idxOf?` and `removeAt`; every
# catalog receipt remains axiom-free.
declare -A EXPECT=(
  ["$P.Payment.PaymentRefusal.sound"]="$NONE"
  ["$P.Payment.checkPayment_accepts_iff"]="$PROPEXT_QUOT"
  ["$P.Payment.PaymentTrace.length_conservation"]="$PROPEXT"
  ["$P.Catalog.PaidGlobalEdge.toCatalog_toGlobal"]="$NONE"
  ["$P.Catalog.PaidGlobalPlan.toCatalog_toGlobal"]="$NONE"
  ["$P.Catalog.exact_catalog_adequate"]="$NONE"
  ["$P.Catalog.exact_complete_globalizes_refusal"]="$NONE"
)

PROMOTED_NONE_RECEIPTS=(
  "$NF.no_free_lift"
  "$NF.no_bridge_no_lift"
  "$NF.lift_is_local_or_paid"
  "$NF.paid_lift_sound"
  "$NF.naked_lift_unsound"
  "$D.derivation_extends_along_paid_path"
  "$D.cut_admissible"
  "$D.lift_floor_mono"
  "$D.revoked_floor_derives_nothing"
  "$D.witnessed_metatheory"
  "$S.hyp"
  "$S.floor"
  "$S.cross"
  "$S.of_lift"
  "$S.empty_iff_lift"
  "$S.iff_lift_context_floor"
  "$S.weaken_of_subset"
  "$S.extends_along_paid_path"
  "$S.sound"
  "$S.empty_floor_empty_context_derives_nothing"
  "$RS.split_residual_prefix"
  "$RS.mem_input_of_mem_consumed"
  "$RS.mem_input_of_mem_residual"
  "$RS.mem_residual_of_mem_input_not_consumed"
  "$RS.residual_mem_input"
  "$RS.weaken_prefix_admissible"
  "$RS.empty_input_derives_nothing"
  "$RS.single_claim_does_not_survive_use"
  "$RS.bridge_token_suffices"
  "$RS.ordinary_crosses_from_valid_bridge"
)
PROMOTED_PROPEXT_RECEIPTS=(
  "$S.weaken_append_right"
  "$S.weaken_append_left"
  "$S.cut_admissible"
  "$RS.claim_mem_claimAssumptions_of_formula_mem"
  "$RS.residue_preserved"
  "$RS.erases_to_sequent"
  "$RS.cannot_cross_without_bridge_token_any_delta"
  "$RS.cannot_cross_without_bridge_token"
  "$RS.ordinary_reachability_not_resource_executability_without_token"
  "$RC.removeAt_sound"
  "$RC.split_to_removeAt"
  "$RC.checks_sound"
  "$RC.checks_complete"
  "$RC.checks_iff_derives"
  "$RC.validated_denial_sound"
)
for receipt in "${PROMOTED_NONE_RECEIPTS[@]}"; do EXPECT["$receipt"]="$NONE"; done
for receipt in "${PROMOTED_PROPEXT_RECEIPTS[@]}"; do EXPECT["$receipt"]="$PROPEXT"; done

PAID_API=(
  "$P.Payment.PaymentTrace"
  "$P.Payment.PaymentRefusal"
  "$P.Payment.PaymentRefusal.sound"
  "$P.Payment.checkPayment"
  "$P.Payment.checkPayment_accepts_iff"
  "$P.Payment.PaymentTrace.length_conservation"
  "$P.Catalog.PaidGlobalEdge"
  "$P.Catalog.PaidCatalogEdge"
  "$P.Catalog.ExactPaidCatalogComplete"
  "$P.Catalog.PaidCatalogEdge.toGlobal"
  "$P.Catalog.PaidGlobalEdge.toCatalog"
  "$P.Catalog.PaidGlobalEdge.toCatalog_toGlobal"
  "$P.Catalog.PaidGlobalPlan"
  "$P.Catalog.PaidCatalogPlan"
  "$P.Catalog.PaidCatalogPlan.certifiedEdge"
  "$P.Catalog.PaidCatalogPlan.toGlobal"
  "$P.Catalog.PaidGlobalPlan.toCatalog"
  "$P.Catalog.PaidGlobalPlan.toCatalog_toGlobal"
  "$P.Catalog.exact_catalog_adequate"
  "$P.Catalog.exact_complete_globalizes_refusal"
)
PAID_RECEIPTS=(
  "$P.Payment.PaymentRefusal.sound"
  "$P.Payment.checkPayment_accepts_iff"
  "$P.Payment.PaymentTrace.length_conservation"
  "$P.Catalog.PaidGlobalEdge.toCatalog_toGlobal"
  "$P.Catalog.PaidGlobalPlan.toCatalog_toGlobal"
  "$P.Catalog.exact_catalog_adequate"
  "$P.Catalog.exact_complete_globalizes_refusal"
)

# Entire public named surface of the five checker/WDC foundation modules:
# 15 types/definitions, all 18 constructors, and all 45 public theorems.
PROMOTED_API=(
  "$NF.Lift"
  "$NF.PaidFrom"
  "$NF.BridgeValid"
  "$NF.NakedLift"
  "$D.Derivable"
  "$S.Context"
  "$S.Derivable"
  "$RS.ResourceFormula"
  "$RS.Context"
  "$RS.Split"
  "$RS.Consumes"
  "$RS.claimAssumptions"
  "$RS.Derives"
  "$RC.removeAt"
  "$RC.Checks"
  "$NF.Lift.base"
  "$NF.Lift.cross"
  "$NF.PaidFrom.refl"
  "$NF.PaidFrom.step"
  "$NF.NakedLift.base"
  "$NF.NakedLift.jump"
  "$RS.ResourceFormula.claim"
  "$RS.ResourceFormula.bridge"
  "$RS.ResourceFormula.residue"
  "$RS.Split.nil"
  "$RS.Split.left"
  "$RS.Split.right"
  "$RS.Derives.floor"
  "$RS.Derives.hyp"
  "$RS.Derives.bridge"
  "$RC.Checks.floor"
  "$RC.Checks.hyp"
  "$RC.Checks.bridge"
  "${PROMOTED_NONE_RECEIPTS[@]}"
  "${PROMOTED_PROPEXT_RECEIPTS[@]}"
)
API=("${PAID_API[@]}" "${PROMOTED_API[@]}")
RECEIPTS=(
  "${PAID_RECEIPTS[@]}"
  "${PROMOTED_NONE_RECEIPTS[@]}"
  "${PROMOTED_PROPEXT_RECEIPTS[@]}"
)

TMP="$(mktemp "${TMPDIR:-/tmp}/paid-recomposition-footprint-XXXXXX.lean")"
trap 'rm -f "$TMP"' EXIT
{
  echo "import $ROOT_MODULE"
  echo "open scoped $D"
  echo "open scoped $S"
  for declaration in "${API[@]}"; do
    echo "#check $declaration"
  done
  echo '#check fun (K : Bool → Prop) (B : Bool → Bool → Prop) (c : Bool) => (K ⊢[B] c)'
  echo '#check fun (Γ : List Bool) (K : Bool → Prop) (B : Bool → Bool → Prop) (c : Bool) => (Γ |--[K,B] c)'
  for receipt in "${RECEIPTS[@]}"; do
    echo "#print axioms $receipt"
  done
} > "$TMP"

if ! OUT="$(lake env lean "$TMP" 2>&1)"; then
  echo "$OUT" >&2
  echo "FAIL: PaidRecomposition frozen API/footprint probe did not elaborate" >&2
  exit 4
fi

if grep -q 'sorryAx' <<<"$OUT"; then
  echo "$OUT" >&2
  echo "FAIL: a PaidRecomposition receipt depends on sorryAx" >&2
  exit 5
fi

fail=0
normalized_report() {
  local receipt="$1"
  awk -v target="'$receipt'" '
    index($0, target) == 1 { capture = 1 }
    capture {
      printf "%s ", $0
      if ($0 ~ /does not depend on any axioms/ || $0 ~ /\]$/) exit
    }
  ' <<<"$OUT" |
    sed -E "s/^'[^']+' //; s/[[:space:]]+/ /g; s/ $//"
}

for receipt in "${RECEIPTS[@]}"; do
  expected="${EXPECT[$receipt]}"
  actual="$(normalized_report "$receipt")"
  if [ "$actual" != "$expected" ]; then
    echo "FAIL: $receipt" >&2
    echo "      expected: $expected" >&2
    echo "      actual:   ${actual:-<missing or renamed receipt>}" >&2
    fail=1
  fi
done

if [ "$fail" -ne 0 ]; then exit 5; fi

echo "PASS — PaidRecomposition stable surface: exact 8 PUBLIC/3 ANNEX custody, exact isolated Mathlib/SCRATCH-free closure (${#seen[@]} modules), fenced evidence target green/non-default, ${#API[@]} frozen public names plus 2 scoped notations, and ${#RECEIPTS[@]} exact classified theorem footprints (promoted foundation: ${#PROMOTED_NONE_RECEIPTS[@]} axiom-free/${#PROMOTED_PROPEXT_RECEIPTS[@]} propext)"
