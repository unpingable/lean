#!/usr/bin/env bash
set -euo pipefail

FORMAL_ROOT="$(cd "$(dirname "$0")" && pwd)"
REPO_ROOT="$(cd "$FORMAL_ROOT/../.." && pwd)"
cd "$FORMAL_ROOT"

lake -d "$REPO_ROOT" build NightshiftGovernedAuthorizationQualification
lake -d "$REPO_ROOT" env lean NightshiftGovernedAuthorization.lean
lake -d "$REPO_ROOT" env lean NightshiftGovernedAuthorizationProvenance.lean
lake -d "$REPO_ROOT" env lean NightshiftDecisionBasisAdequacy.lean
lake -d "$REPO_ROOT" env lean NightshiftObservationCurrentness.lean

if rg -n '\b(sorry|admit|native_decide)\b' --glob '*.lean' .; then
  echo 'hygiene failure: sorry/admit/native_decide found' >&2
  exit 1
fi

if rg -n '^[[:space:]]*axiom[[:space:]]' --glob '*.lean' .; then
  echo 'hygiene failure: custom axiom declaration found' >&2
  exit 1
fi

echo 'Nightshift governed-authorization qualification checks passed.'
