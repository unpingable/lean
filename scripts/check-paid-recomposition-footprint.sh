#!/usr/bin/env bash
# Ratified v11 gate for the stable PaidRecomposition theorem family.
#
# This gate fails closed over custody, the stable import boundary, the frozen
# public API names, exact theorem axiom footprints, and the Mathlib/SCRATCH-free
# import closure. Applications and countermodels are registered evidence, but
# are deliberately absent from the stable root and `Witnessed` build target.
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
PUBLIC_APP_FILE="LeanProofs/Witnessed/PaidRecomposition/Applications/ResourceTraceOneCrossing.lean"
COUNTERMODEL_FILE="LeanProofs/Witnessed/PaidRecomposition/Countermodels/EndpointCompleteness.lean"
FINITE_SUPPORT_FILE="LeanProofs/Witnessed/PaidRecomposition/Applications/FiniteSupportOneCrossing.lean"

declare -A EXPECTED_CUSTODY=(
  ["$ROOT_FILE"]="PUBLIC-SHIPPED"
  ["$PAYMENT_FILE"]="PUBLIC-SHIPPED"
  ["$CATALOG_FILE"]="PUBLIC-SHIPPED"
  ["$PUBLIC_APP_FILE"]="ANNEX"
  ["$COUNTERMODEL_FILE"]="ANNEX"
  ["$FINITE_SUPPORT_FILE"]="ANNEX"
)
ALL_FILES=(
  "$ROOT_FILE"
  "$PAYMENT_FILE"
  "$CATALOG_FILE"
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

if grep -nE '^[[:space:]]*import[[:space:]]+LeanProofs\.Scratch' \
    "$ROOT_FILE" "$PAYMENT_FILE" "$CATALOG_FILE" \
    "$PUBLIC_APP_FILE" "$COUNTERMODEL_FILE" >/dev/null; then
  echo "FAIL: stable/public PaidRecomposition custody imports SCRATCH" >&2
  grep -nE '^[[:space:]]*import[[:space:]]+LeanProofs\.Scratch' \
    "$ROOT_FILE" "$PAYMENT_FILE" "$CATALOG_FILE" \
    "$PUBLIC_APP_FILE" "$COUNTERMODEL_FILE" >&2 || true
  exit 1
fi
if [ "$(grep -cE '^[[:space:]]*import[[:space:]]+LeanProofs\.Scratch\.FiniteSupportChecker([[:space:]]|$)' "$FINITE_SUPPORT_FILE" || true)" -ne 1 ]; then
  echo "FAIL: finite-support ANNEX must expose exactly one direct SCRATCH checker import" >&2
  exit 1
fi

# Root means exactly two imports, in the frozen order.
EXPECTED_ROOT_IMPORTS=("$PAYMENT_MODULE" "$CATALOG_MODULE")
mapfile -t root_imports < <(awk '
  /^[[:space:]]*import[[:space:]]/ {
    for (i = 2; i <= NF; i++) {
      if ($i == "--") break
      print $i
    }
  }
' "$ROOT_FILE")
if [ "${#root_imports[@]}" -ne "${#EXPECTED_ROOT_IMPORTS[@]}" ]; then
  echo "FAIL: stable root must import exactly Payment and Catalog" >&2
  printf '  actual: %s\n' "${root_imports[*]:-<none>}" >&2
  exit 2
fi
for i in "${!EXPECTED_ROOT_IMPORTS[@]}"; do
  if [ "${root_imports[$i]}" != "${EXPECTED_ROOT_IMPORTS[$i]}" ]; then
    echo "FAIL: stable root import order/content drifted" >&2
    printf '  expected: %s\n' "${EXPECTED_ROOT_IMPORTS[*]}" >&2
    printf '  actual:   %s\n' "${root_imports[*]}" >&2
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
for module in "$ROOT_MODULE" "$PAYMENT_MODULE" "$CATALOG_MODULE"; do
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
  done < <(awk '
    /^[[:space:]]*import[[:space:]]/ {
      for (i = 2; i <= NF; i++) {
        if ($i == "--") break
        print $i
      }
    }
  ' "$file")
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

if ! lake build Witnessed "$ROOT_MODULE" PaidRecompositionEvidence >/dev/null 2>&1; then
  echo "FAIL: stable Witnessed/PaidRecomposition or fenced evidence build did not succeed" >&2
  exit 3
fi

NONE="does not depend on any axioms"
PROPEXT="depends on axioms: [propext]"
PROPEXT_QUOT="depends on axioms: [propext, Quot.sound]"

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

API=(
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
RECEIPTS=(
  "$P.Payment.PaymentRefusal.sound"
  "$P.Payment.checkPayment_accepts_iff"
  "$P.Payment.PaymentTrace.length_conservation"
  "$P.Catalog.PaidGlobalEdge.toCatalog_toGlobal"
  "$P.Catalog.PaidGlobalPlan.toCatalog_toGlobal"
  "$P.Catalog.exact_catalog_adequate"
  "$P.Catalog.exact_complete_globalizes_refusal"
)

TMP="$(mktemp "${TMPDIR:-/tmp}/paid-recomposition-footprint-XXXXXX.lean")"
trap 'rm -f "$TMP"' EXIT
{
  echo "import $ROOT_MODULE"
  for declaration in "${API[@]}"; do
    echo "#check $declaration"
  done
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

echo "PASS — PaidRecomposition stable surface: exact 3/3 custody, isolated Mathlib/SCRATCH-free closure (${#seen[@]} modules), fenced evidence target green/non-default, ${#API[@]} frozen API names, and ${#RECEIPTS[@]} exact classified receipt footprints"
