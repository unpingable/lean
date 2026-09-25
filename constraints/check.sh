#!/usr/bin/env bash
# Gate for the `constraints/` public-evidence family (Lake target
# `DesignConstraints`).  Builds the target, forbids `sorry`, local axioms,
# `native_decide` and the other non-kernel escape hatches, requires that the
# family imports nothing outside itself, and re-attests the axiom footprint of
# every named result: no `sorryAx`, and nothing beyond Lean's core axioms.
#
# Pass/fail is the exit code.  Passing is compile evidence for the stated
# theorems only; it is not a conformance claim about any system.
set -euo pipefail

FAMILY_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
REPO_ROOT="$(cd "$FAMILY_ROOT/.." && pwd -P)"
QUALIFICATION="$FAMILY_ROOT/DesignConstraintsQualification.lean"

cd "$REPO_ROOT"
lake build DesignConstraints

if grep -rn --include='*.lean' \
    -E '\bsorry\b|^\s*axiom\b|\bnative_decide\b|^\s*opaque\b|^\s*unsafe\b|^\s*partial\s+def\b' \
    "$FAMILY_ROOT"; then
  echo "constraints gate FAILED: non-kernel construct above" >&2
  exit 1
fi

if grep -rhn --include='*.lean' -E '^[[:space:]]*import[[:space:]]' "$FAMILY_ROOT" \
    | sed -E 's/^[0-9]+://; s/^[[:space:]]*import[[:space:]]+//' \
    | sort -u \
    | grep -vE '^(DecisionSemantics|Resources|Authority)\.[A-Za-z]+$'; then
  echo "constraints gate FAILED: unexpected import above" >&2
  exit 1
fi

axiom_log="$(mktemp)"
trap 'rm -f "$axiom_log"' EXIT
(cd "$FAMILY_ROOT" && lake -d "$REPO_ROOT" env lean "$QUALIFICATION") > "$axiom_log"

if grep -n "sorryAx\|declaration uses 'sorry'" "$axiom_log"; then
  echo "constraints gate FAILED: a theorem depends on sorry" >&2
  exit 1
fi

flat="$(tr '\n' ' ' < "$axiom_log")"
directives="$(grep -c '^#print axioms' "$QUALIFICATION")"
responses="$(printf '%s' "$flat" \
  | grep -oE "depends on axioms: \[[^]]*\]|does not depend on any axioms" \
  | wc -l)"
if [[ "$directives" -ne "$responses" ]]; then
  echo "constraints gate FAILED: $directives directives, $responses responses" >&2
  exit 1
fi

if printf '%s' "$flat" \
    | grep -oE "depends on axioms: \[[^]]*\]" \
    | sed 's/.*\[//; s/\]//' | tr ',' '\n' | sed 's/^ *//; s/ *$//' \
    | grep -v '^$' | sort -u \
    | grep -vE "^(propext|Classical\.choice|Quot\.sound)$"; then
  echo "constraints gate FAILED: unexpected axiom above" >&2
  exit 1
fi

echo "constraints gate passed"
printf 'axiom footprint over %s audited declarations (distinct):\n' "$directives"
printf '%s' "$flat" \
  | grep -oE "depends on axioms: \[[^]]*\]" \
  | sed 's/.*\[//; s/\]//' | tr ',' '\n' | sed 's/^ *//; s/ *$//' \
  | grep -v '^$' | sort -u | sed 's/^/  /'
printf '  (axiom-free declarations: %s)\n' \
  "$(grep -c 'does not depend on any axioms' "$axiom_log" || true)"
