#!/usr/bin/env bash
# Phase 5 — repo axiom classifier. The repository is NOT axiom-free; it is axiom-classified.
# Every declared `axiom`/`constant` under LeanProofs/ must be classified in axiom-policy.tsv.
# Fail-closed on: unclassified declarations, forbidden-class declarations.
#
# classes (axiom-policy.tsv):
#   signature      — uninterpreted carrier / op / predicate SYMBOL; declares vocabulary, asserts no claim
#   interface-law  — Prop-valued law constraining an abstract interface; allowed only if marked + footprint-visible
#   specimen       — concrete scenario stipulation; allowed only inside a fenced specimen module
#   forbidden      — claim-bodied placeholder (the fake-mustache class); zero tolerance
#
# Exit: 0 PASS, 2 unclassified/forbidden present.
set -euo pipefail
REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$REPO_ROOT"
POLICY="scripts/axiom-policy.tsv"

declare -A CLASS
while IFS=$'\t' read -r path name class _note; do
  [[ -z "${path:-}" || "$path" == \#* ]] && continue
  CLASS["$path|$name"]="$class"
done < "$POLICY"

declare -A COUNT=([signature]=0 [interface-law]=0 [specimen]=0 [forbidden]=0 [unclassified]=0)
fail=0
while IFS= read -r line; do
  file="${line%%:*}"
  rest="${line#*:}"; rest="${rest#*:}"          # strip "path:linenum:"
  name="$(awk '{print $2}' <<<"$rest")"; name="${name%:}"
  cls="${CLASS["$file|$name"]:-unclassified}"
  COUNT["$cls"]=$(( ${COUNT["$cls"]:-0} + 1 ))
  case "$cls" in
    unclassified) echo "FAIL: unclassified axiom/constant — $file :: $name (add to $POLICY)" >&2; fail=1 ;;
    forbidden)    echo "FAIL: FORBIDDEN axiom/constant — $file :: $name (claim-bodied placeholder)" >&2; fail=1 ;;
  esac
done < <(grep -rn "^axiom \|^constant " LeanProofs/ 2>/dev/null || true)

echo "AXIOM AUDIT"
echo "  signature:     ${COUNT[signature]}"
echo "  interface-law: ${COUNT[interface-law]}"
echo "  specimen:      ${COUNT[specimen]}"
echo "  forbidden:     ${COUNT[forbidden]}"
echo "  unclassified:  ${COUNT[unclassified]}"
if [ "$fail" -ne 0 ]; then echo "FAIL"; exit 2; fi
echo "PASS — repo is axiom-classified (not axiom-free); no forbidden or unclassified declarations"
