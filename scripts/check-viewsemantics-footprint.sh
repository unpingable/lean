#!/usr/bin/env bash
# v10 ViewSemantics stable/public-evidence footprint gate. The mathematical/checker/specimen
# receipts must be axiom-free.  The quotient applications may use only their
# disclosed foundations, and the authorized-trace separation receipts must
# have exactly the footprint of the v9 authorization walls they reuse.

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$REPO_ROOT"

if ! lake build ViewSemantics ViewSemanticsEvidence \
    ViewSemanticsEvidenceMathlib >/dev/null 2>&1; then
  echo "FAIL: ViewSemantics stable/evidence targets did not build" >&2
  exit 1
fi

ZERO_RECEIPTS=(
  LeanProofs.ViewSemantics.refines_refl
  LeanProofs.ViewSemantics.refines_trans
  LeanProofs.ViewSemantics.determines_mono
  LeanProofs.ViewSemantics.fiberwiseAmbiguous_notFullyDetermining
  LeanProofs.ViewSemantics.WeakNotStrongCounterexample.notFullyDetermining_does_not_imply_fiberwiseAmbiguous
  LeanProofs.ViewSemantics.CompositionCounterexample.weak_nondetermination_not_closed_under_compose
  LeanProofs.ViewSemantics.CompositionCounterexample.fiberwise_ambiguity_not_closed_under_compose
  LeanProofs.ViewSemantics.CompositionCounterexample.singles_and_pairs_fiberwise_ambiguous_full_determines
  LeanProofs.ViewSemantics.operationallySufficient_required_determines
  LeanProofs.ViewSemantics.deterministicallyBoundedSufficient_iff_refinement_sandwich
  LeanProofs.ViewSemantics.deterministic_bounded_projection_exists_iff
  LeanProofs.ViewSemantics.bounded_action_projection_exists_iff
  LeanProofs.ViewSemantics.withinDisclosureBound_compose
  LeanProofs.ViewSemantics.withinDisclosureBound_finiteJoin
  LeanProofs.ViewSemantics.Examples.all_four_disclosure_sufficiency_cells_inhabited
  LeanProofs.ViewSemantics.consequencePartition_refines_iff
  LeanProofs.ViewSemantics.consequencePartition_factorsThrough_iff_determines
  LeanProofs.ViewSemantics.collapsedSurface_indistinguishable_alt_prevents_identification
  LeanProofs.ViewSemantics.collapsedSurface_collapsedAt_iff_indistinguishable
  LeanProofs.ViewSemantics.witnessInvariance_encapsulated_indistinguishable_iff_determines
  LeanProofs.ViewSemantics.witnessInvariance_movement_implies_notFullyDetermining
  LeanProofs.ViewSemantics.ObligationIndependence.context_reuses_exact_receipt
  LeanProofs.ViewSemantics.Applications.NoSilentProjectionAxis.no_resident_bridge_pair_pays_all_five
  LeanProofs.ViewSemantics.Applications.NoSilentProjectionAxis.projection_receipt_discharges_freshness
  LeanProofs.ViewSemantics.Applications.NoSilentProjectionAxis.exact_projection_bridge_different_view_verdicts
  LeanProofs.ViewSemantics.Applications.NoSilentProjectionAxis.disclosure_is_orthogonal_to_resident_bridge_ontology
  LeanProofs.ViewSemantics.FiniteChecker.checkActionability_actionable_iff
  LeanProofs.ViewSemantics.FiniteChecker.checkActionability_conflict_iff
  LeanProofs.ViewSemantics.FiniteChecker.checkDisclosure_within_iff
  LeanProofs.ViewSemantics.FiniteChecker.checkDisclosure_forbidden_iff
  LeanProofs.ViewSemantics.FiniteCheckerExamples.all_four_checker_cells_evaluate
  MosaicRelease.fiberwise_nonrevelation_not_closed_under_composition
  MosaicRelease.fiberwise_pairwise_nonrevelation_not_closed_under_composition
  CompartmentConflict.blind_view_not_operationally_sufficient
  CompartmentConflict.disclosed_view_is_bounded_sufficient
  CompartmentConflict.disclosed_view_payload_fiberwise_ambiguous
)

QUOTIENT_RECEIPT="LeanProofs.ViewSemantics.Applications.BindingSourceAblation.binding_source_ablation_view_certificate"
P25_RECEIPT="LeanProofs.ViewSemantics.P25Adapter.observationPolicy_determined"
TRACE_REVOKED="LeanProofs.ViewSemantics.DynamicTraceAdapter.full_visibility_does_not_override_revoked_basis"
V9_REVOKED="Admissibility.DynamicTrace.revoked_basis_blocks_dynamic_step"
TRACE_AUTHORITY="LeanProofs.ViewSemantics.DynamicTraceAdapter.full_visibility_does_not_supply_missing_authority"
V9_AUTHORITY="Admissibility.DynamicTrace.step_allowed_without_authority_blocks_dynamic_step"
TRACE_REFINE_REUSE="LeanProofs.ViewSemantics.DynamicTraceAdapter.refineObservation_reuses_trace"
TRACE_JOIN_REUSE="LeanProofs.ViewSemantics.DynamicTraceAdapter.joinObservation_reuses_trace"
V9_TRACE_BASELINE="Admissibility.DynamicTrace.traceSteps"

TMP="$(mktemp "${TMPDIR:-/tmp}/viewsemantics-footprint-XXXXXX.lean")"
trap 'rm -f "$TMP"' EXIT
{
  echo "import LeanProofs.ViewSemantics"
  echo "import LeanProofs.ViewSemantics.Evidence"
  echo "import LeanProofs.ViewSemantics.EvidenceMathlib"
  for receipt in "${ZERO_RECEIPTS[@]}"; do
    echo "#print axioms $receipt"
  done
  echo "#print axioms $QUOTIENT_RECEIPT"
  echo "#print axioms $P25_RECEIPT"
  echo "#print axioms $TRACE_REVOKED"
  echo "#print axioms $V9_REVOKED"
  echo "#print axioms $TRACE_AUTHORITY"
  echo "#print axioms $V9_AUTHORITY"
  echo "#print axioms $TRACE_REFINE_REUSE"
  echo "#print axioms $TRACE_JOIN_REUSE"
  echo "#print axioms $V9_TRACE_BASELINE"
} > "$TMP"

if ! OUT="$(lake env lean "$TMP" 2>&1)"; then
  echo "$OUT" >&2
  echo "FAIL: footprint probe did not compile" >&2
  exit 2
fi

if grep -q 'sorryAx' <<<"$OUT"; then
  echo "FAIL: a ViewSemantics receipt depends on sorryAx" >&2
  exit 3
fi

fail=0
for receipt in "${ZERO_RECEIPTS[@]}"; do
  if ! grep -Fq "'$receipt' does not depend on any axioms" <<<"$OUT"; then
    echo "FAIL: expected axiom-free receipt: $receipt" >&2
    grep -F "'$receipt'" <<<"$OUT" >&2 || true
    fail=1
  fi
done

normalized_report() {
  local receipt="$1"
  awk -v target="'$receipt'" '
    index($0, target) == 1 { capture = 1 }
    capture {
      printf "%s ", $0
      if ($0 ~ /does not depend on any axioms/ || $0 ~ /\]$/) exit
    }
  ' <<<"$OUT" | sed -E "s/^'[^']+' //; s/[[:space:]]+/ /g; s/ $//"
}

quotient_report="$(normalized_report "$QUOTIENT_RECEIPT")"
if [ "$quotient_report" != "depends on axioms: [propext, Quot.sound]" ]; then
  echo "FAIL: non-XOR application footprint drifted from [propext, Quot.sound]" >&2
  echo "  actual: ${quotient_report:-<missing>}" >&2
  fail=1
fi

p25_report="$(normalized_report "$P25_RECEIPT")"
if [ "$p25_report" != \
    "depends on axioms: [propext, Classical.choice, Quot.sound]" ]; then
  echo "FAIL: P25 adapter footprint drifted from [propext, Classical.choice, Quot.sound]" >&2
  echo "  actual: ${p25_report:-<missing>}" >&2
  fail=1
fi

trace_revoked_report="$(normalized_report "$TRACE_REVOKED")"
v9_revoked_report="$(normalized_report "$V9_REVOKED")"
if [ -z "$trace_revoked_report" ] || [ "$trace_revoked_report" != "$v9_revoked_report" ]; then
  echo "FAIL: revoked-basis trace adapter added or lost foundations" >&2
  echo "  adapter: ${trace_revoked_report:-<missing>}" >&2
  echo "  v9 wall: ${v9_revoked_report:-<missing>}" >&2
  fail=1
fi

trace_authority_report="$(normalized_report "$TRACE_AUTHORITY")"
v9_authority_report="$(normalized_report "$V9_AUTHORITY")"
if [ -z "$trace_authority_report" ] || \
    [ "$trace_authority_report" != "$v9_authority_report" ]; then
  echo "FAIL: missing-authority trace adapter added or lost foundations" >&2
  echo "  adapter: ${trace_authority_report:-<missing>}" >&2
  echo "  v9 wall: ${v9_authority_report:-<missing>}" >&2
  fail=1
fi

v9_trace_report="$(normalized_report "$V9_TRACE_BASELINE")"
for receipt in "$TRACE_REFINE_REUSE" "$TRACE_JOIN_REUSE"; do
  reuse_report="$(normalized_report "$receipt")"
  if [ -z "$reuse_report" ] || [ "$reuse_report" != "$v9_trace_report" ]; then
    echo "FAIL: trace-reuse receipt added or lost foundations: $receipt" >&2
    echo "  adapter: ${reuse_report:-<missing>}" >&2
    echo "  v9 base: ${v9_trace_report:-<missing>}" >&2
    fail=1
  fi
done

if [ "$fail" -ne 0 ]; then exit 4; fi

echo "PASS — ${#ZERO_RECEIPTS[@]} stable/evidence receipts axiom-free; quotient/P25 footprints exact; trace receipts match their v9 walls"
