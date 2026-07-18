#!/usr/bin/env bash
# Re-attest the Admissibility.Calculus axiom footprint in the canonical
# build context. Fail-closed: every frozen receipt must report EXACTLY its
# documented footprint. This is what prevents the Calculus stable root
# (rungs 2-6 of the promotion campaign) from quietly growing an axiom, a
# sorry, an import, or a renamed receipt. Exit code is the gate, never
# eyeballed.
#
# Source of truth for the expected footprints: the rung-2/3/4/5/6 candidate
# packets and hostile reviews (skunkworks
# ADMISSIBILITY_CALCULUS_RUNG{2,3,4}_*_CANDIDATE_2026-07-17.md,
# ADMISSIBILITY_CALCULUS_RUNG5_INDEXED_COMPARISON_REVISED_CANDIDATE_
# 2026-07-18.md, and
# ADMISSIBILITY_CALCULUS_RUNG6_STORED_DECISION_CROSSING_CANDIDATE_
# 2026-07-18.md), recorded
# in CLAIM-REGISTER.md entries #20/#21/#22/#23/#24 and the `#print axioms`
# receipts in the modules themselves. The frozen surface is 90 receipts:
# six rung-2 core receipts (all axiom-free), sixteen rung-3 instance
# receipts (ten axiom-free, six exactly `[propext]`), twenty-three rung-4
# spine receipts (eighteen axiom-free, five exactly `[propext]`), and
# seventeen rung-5 comparison-framework receipts (all axiom-free; the
# concrete seven-entry ledger stays research-tree evidence), and
# twenty-eight rung-6 stored-decision crossing receipts (fourteen generic
# axiom-free, fourteen concrete exactly `[propext]`; decide once, derive
# everything from the stored pair).
# `no_claim_erasing_check_is_faithful`, `boundedPaidReachability`, and the
# seven rung-4 pre-freeze renames are the operator-ratified names.
#
# Exit codes:
#   0 — stable root builds; all 90 receipts exact
#   1 — `lake build AdmissibilityCalculus` failed
#   2 — a receipt drifted (missing/renamed, new axiom, sorry, or wrong footprint)

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$REPO_ROOT"

P="Admissibility.Calculus.GovernedFamily"
C="Admissibility.Calculus"
M="Admissibility.Calculus.Comparison"
X="Admissibility.Calculus.Crossing"
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
  # rung 4 — generic spine, 15 (13 axiom-free + 2 propext)
  ["$C.SpineEncoding.funnel_of_decide_inl"]="$NONE"
  ["$C.SpineEncoding.funnel_of_decide_inr"]="$NONE"
  ["$C.SpineEncoding.refusal_singleton_ne_clean"]="$NONE"
  ["$C.SpineEncoding.funnel_decision_branches_ne"]="$NONE"
  ["$C.SpineEncoding.funnel_authority_iff"]="$NONE"
  ["$C.SpineEncoding.funnel_refusing_emits_domain_obstruction"]="$NONE"
  ["$C.SpineEncoding.funnel_never_opaque"]="$NONE"
  ["$C.SpineEncoding.funnel_emits_no_core_obstruction"]="$PROPEXT"
  ["$C.LosslessEncoding.decode_encodePacket"]="$NONE"
  ["$C.LosslessEncoding.decode_some_iff"]="$NONE"
  ["$C.LosslessEncoding.decode_none_iff_not_encoded"]="$NONE"
  ["$C.LosslessEncoding.encodePacket_injective"]="$NONE"
  ["$C.LosslessEncoding.distinct_refusals_encode_distinct"]="$NONE"
  ["$C.LosslessEncoding.no_subsingleton_domain_of_distinct_refusals"]="$NONE"
  ["$C.LosslessEncoding.refusal_recoverable"]="$PROPEXT"
  # rung 4 — Weathering exact spine, 4, all axiom-free
  ["$W.weather_decode_encode"]="$NONE"
  ["$W.weather_encode_decode"]="$NONE"
  ["$W.weather_funnel_sound_natively"]="$NONE"
  ["$W.weather_funnel_distinguishes_stale_and_retired"]="$NONE"
  # rung 4 — BoundedPaidReachability exact spine, 4 (1 axiom-free + 3 propext)
  ["$B.bounded_paid_funnel_sound_natively"]="$PROPEXT"
  ["$B.bounded_paid_decide_from_bare_returns_exact_barrier"]="$PROPEXT"
  ["$B.bounded_paid_bare_refusal_round_trip"]="$PROPEXT"
  ["$B.bounded_paid_no_barrier_for_funded"]="$NONE"
  # rung 5 — indexed comparison framework, 17, all axiom-free
  ["$M.mem_allEntries"]="$NONE"
  ["$M.allEntries_nodup"]="$NONE"
  ["$M.allEntries_length"]="$NONE"
  ["$M.ExactJudgmentReceipt.preserves"]="$NONE"
  ["$M.ExactJudgmentReceipt.reflects"]="$NONE"
  ["$M.ExactRepresentationReceipt.map_injective"]="$NONE"
  ["$M.ExactRepresentationReceipt.decode_some_iff"]="$NONE"
  ["$M.DirectionalWithLossReceipt.no_left_inverse"]="$NONE"
  ["$M.SeparationReceipt.not_universal_preservation"]="$NONE"
  ["$M.CapabilityDisposition.receipt_of_supported"]="$NONE"
  ["$M.CapabilityDisposition.unsupported_not_supported"]="$NONE"
  ["$M.CapabilityDisposition.no_support_without_receipt"]="$NONE"
  ["$M.CapabilityBook.receipt"]="$NONE"
  ["$M.Ledger.covers"]="$NONE"
  ["$M.collapsed_map_rejects_exact_representation"]="$NONE"
  ["$M.constant_map_rejects_exact_representation"]="$NONE"
  ["$M.impossible_capability_has_no_supported_disposition"]="$NONE"
  # rung 6 — stored-decision crossing core, 14, all axiom-free
  ["$X.CheckedCrossing.result_isLeft_iff_authority"]="$NONE"
  ["$X.authority_iff_components"]="$NONE"
  ["$X.refusal_refutes_authority"]="$NONE"
  ["$X.authority_requires_both_standings"]="$NONE"
  ["$X.authority_preserves_both_custodies"]="$NONE"
  ["$X.CheckedCrossing.verdict_authority_iff_result"]="$NONE"
  ["$X.CheckedCrossing.verdict_authority_iff"]="$NONE"
  ["$X.CheckedCrossing.located_forget"]="$NONE"
  ["$X.CheckedCrossing.located_authority_iff"]="$NONE"
  ["$X.left_refusal_encoding_decodes"]="$NONE"
  ["$X.right_refusal_encoding_decodes"]="$NONE"
  ["$X.CheckedCrossing.left_refusal_located_and_decode"]="$NONE"
  ["$X.CheckedCrossing.right_refusal_located_and_decode"]="$NONE"
  ["$X.CheckedCrossing.both_refusals_located_and_decode"]="$NONE"
  # rung 6 — Weathering/bounded-paid crossing leaf, 14, exactly [propext]
  ["$X.check_fresh_funded_exact"]="$PROPEXT"
  ["$X.check_stale_funded_exact"]="$PROPEXT"
  ["$X.check_fresh_bare_exact"]="$PROPEXT"
  ["$X.check_stale_bare_exact"]="$PROPEXT"
  ["$X.weathering_paid_authority_iff_components"]="$PROPEXT"
  ["$X.green_gate_cannot_cure_unfunded_passage"]="$PROPEXT"
  ["$X.funded_passage_cannot_cure_stale_gate"]="$PROPEXT"
  ["$X.weathering_paid_requires_both_standings"]="$PROPEXT"
  ["$X.weathering_paid_preserves_both_custodies"]="$PROPEXT"
  ["$X.bounded_paid_component_custody_is_vacuous"]="$PROPEXT"
  ["$X.weathering_paid_component_obligation_books_are_empty"]="$PROPEXT"
  ["$X.stale_funded_location_exact"]="$PROPEXT"
  ["$X.fresh_bare_location_exact"]="$PROPEXT"
  ["$X.stale_bare_double_fault_nonshadowing"]="$PROPEXT"
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
