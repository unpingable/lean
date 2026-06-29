#!/usr/bin/env bash
# Phase 5 — native_decide policy gate. Allowed ONLY in finite-witness modules listed in
# native-decide-policy.tsv (finite computational traces). Forbidden in WDC / Admissibility
# kernels / structural public receipts. Not a purity cult — a classifier.
# Exit: 0 PASS, 2 a native_decide appears outside an allowed module.
set -euo pipefail
REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$REPO_ROOT"
POLICY="scripts/native-decide-policy.tsv"

declare -A ALLOWED
while IFS=$'\t' read -r path _note; do
  [[ -z "${path:-}" || "$path" == \#* ]] && continue
  ALLOWED["$path"]=1
done < "$POLICY"

fail=0; total=0
# Count only ACTUAL tactic uses: exclude full-line `--` comments and backticked prose
# mentions (convention: code tokens in prose/doc-comments are written `native_decide`).
while IFS= read -r line; do
  file="${line%%:*}"
  total=$(( total + 1 ))
  if [[ -n "${ALLOWED["$file"]:-}" ]]; then
    echo "  allowed (finite witness): $line"
  else
    echo "FAIL: native_decide outside allowed finite-witness modules — $line" >&2; fail=1
  fi
done < <(grep -rn "native_decide" LeanProofs/ 2>/dev/null | grep -vE ':[0-9]+:[[:space:]]*--' | grep -vF '`native_decide`' || true)

echo "NATIVE_DECIDE AUDIT: $total occurrence(s)"
if [ "$fail" -ne 0 ]; then echo "FAIL"; exit 2; fi
echo "PASS — native_decide confined to allowed finite-witness modules"
