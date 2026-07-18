#!/usr/bin/env bash
# Re-attest the PathVerdict rung-1 axiom footprint in the canonical build
# context. Fail-closed: every frozen receipt must report EXACTLY its
# documented footprint. This is what prevents the Mathlib-free Domains and
# Located surfaces (Admissibility Calculus promotion rung 1) from quietly
# growing a new axiom, a sorry, or a renamed receipt. Exit code is the gate,
# never eyeballed.
#
# Source of truth for the expected footprints: the rung-1 candidate packet
# and hostile review of 2026-07-17 (skunkworks
# ADMISSIBILITY_CALCULUS_RUNG1_DOMAINS_LOCATED_CANDIDATE_2026-07-17.md),
# recorded in CLAIM-REGISTER.md entry #19 and the `#print axioms` receipts
# in the modules themselves. The frozen surface is 24 Domains theorems plus
# 12 Located theorems; 35 are axiom-free and `mixed_compose_authority_iff`
# uses only [propext].
#
# Exit codes:
#   0 — stable root and evidence build; all 36 receipts exact
#   1 — `lake build PathVerdict PathVerdictEvidence` failed
#   2 — a receipt drifted (missing/renamed, new axiom, sorry, or wrong footprint)

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$REPO_ROOT"

P="Admissibility.PathVerdict"
NONE="does not depend on any axioms"
PROPEXT="depends on axioms: [propext]"

# Frozen receipt -> expected footprint (EXACT).
declare -A EXPECT=(
  # Domains — 24
  ["$P.ObstructionKind.mapDomain_id"]="$NONE"
  ["$P.ObstructionKind.mapDomain_comp"]="$NONE"
  ["$P.PathVerdict.mapDomain_id"]="$NONE"
  ["$P.PathVerdict.mapDomain_comp"]="$NONE"
  ["$P.EdgeVerdict.mapDomain_id"]="$NONE"
  ["$P.EdgeVerdict.mapDomain_comp"]="$NONE"
  ["$P.EdgeVerdict.mapDomain_eq_bridge_iff"]="$NONE"
  ["$P.PathVerdict.mapDomain_compose"]="$NONE"
  ["$P.PathVerdict.mapDomain_clean"]="$NONE"
  ["$P.EdgeVerdict.obstruction?_mapDomain"]="$NONE"
  ["$P.fold_mapDomain"]="$NONE"
  ["$P.mapDomain_authority_iff"]="$NONE"
  ["$P.mem_mapDomain_of_mem"]="$NONE"
  ["$P.core_mem_mapDomain_iff"]="$NONE"
  ["$P.domain_mem_mapDomain_iff"]="$NONE"
  ["$P.inl_authority_iff"]="$NONE"
  ["$P.inr_authority_iff"]="$NONE"
  ["$P.inl_mem_iff"]="$NONE"
  ["$P.inr_mem_iff"]="$NONE"
  ["$P.inl_fabricates_no_right_sin"]="$NONE"
  ["$P.inr_fabricates_no_left_sin"]="$NONE"
  ["$P.mixed_compose_authority_iff"]="$PROPEXT"
  ["$P.obstruction_blocks_mixed_left"]="$NONE"
  ["$P.obstruction_blocks_mixed_right"]="$NONE"
  # Located — 12
  ["$P.LocatedVerdict.clean_compose"]="$NONE"
  ["$P.LocatedVerdict.compose_clean"]="$NONE"
  ["$P.LocatedVerdict.compose_assoc"]="$NONE"
  ["$P.forget_foldLocated"]="$NONE"
  ["$P.located_authority_iff"]="$NONE"
  ["$P.foldLocated_append"]="$NONE"
  ["$P.foldLocated_carries"]="$NONE"
  ["$P.foldLocated_sound"]="$NONE"
  ["$P.located_obstruction_blocks"]="$NONE"
  ["$P.located_pinpoints"]="$NONE"
  ["$P.mapId_forget"]="$NONE"
  ["$P.mapId_authority_iff"]="$NONE"
)

# 1. The stable root and its public evidence must build. Both libs are
#    Mathlib-free by construction, so a green build also proves isolation held.
if ! lake build PathVerdict PathVerdictEvidence >/dev/null 2>&1; then
  echo "FAIL: lake build PathVerdict PathVerdictEvidence did not succeed" >&2
  exit 1
fi

# 2. Probe the footprint via `#print axioms` against the built oleans.
TMP="$(mktemp "${TMPDIR:-/tmp}/pathverdict-footprint-XXXXXX.lean")"
trap 'rm -f "$TMP"' EXIT
{
  echo "import LeanProofs.Admissibility.PathVerdict"
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

echo "OK: PathVerdict root builds; all ${#EXPECT[@]} rung-1 receipts within their attested footprint"
