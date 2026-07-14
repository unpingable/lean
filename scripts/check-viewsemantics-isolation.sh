#!/usr/bin/env bash
# Candidate v10 campaign isolation gate.  The default `ViewSemantics` target
# must remain Mathlib-free and every module owned by the candidate surface must
# carry its unratified custody marker.  P25 is built through the explicit
# `ViewSemanticsMathlibIslands` target instead of leaking into this closure.

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$REPO_ROOT"

module_path() { echo "${1//./\/}.lean"; }

status=0
core_count=0
application_count=0

audit_target() {
  local target="$1"
  local boundary="$2"
  local target_roots
  target_roots=$(awk -v target="$target" '
    /^name = / { in_target = ($0 == "name = \"" target "\"") }
    in_target && /^roots = \[/ { collecting = 1; next }
    collecting && /^\]/ { collecting = 0; in_target = 0 }
    collecting { gsub(/[", ]/, ""); if (length($0) > 0) print }
  ' lakefile.toml)

  if [ -z "$target_roots" ]; then
    echo "FAIL: could not extract roots for lean_lib $target" >&2
    status=1
    return
  fi

  local -A seen=()
  local -a queue=()
  local -a missing=()
  local -a mathlib_offenders=()
  local -a p25_offenders=()
  local -a boundary_offenders=()
  local module file imported
  for module in $target_roots; do queue+=("$module"); done

  while [ ${#queue[@]} -gt 0 ]; do
    module="${queue[0]}"
    queue=("${queue[@]:1}")
    [ -n "${seen[$module]:-}" ] && continue
    seen[$module]=1

    case "$module" in
      LeanProofs.Paper25EpistemicBorderControl|LeanProofs.ViewSemantics.P25Adapter)
        p25_offenders+=("$module")
        ;;
    esac

    if [ "$boundary" = "core" ]; then
      case "$module" in
        LeanProofs.ViewSemantics.Applications|LeanProofs.ViewSemantics.Applications.*|LeanProofs.Scratch.*)
          boundary_offenders+=("$module")
          ;;
      esac
    else
      case "$module" in
        LeanProofs.Scratch.BindingSourceAblation|LeanProofs.Scratch.NoSilentProjection)
          ;;
        LeanProofs.Scratch.*)
          boundary_offenders+=("$module")
          ;;
      esac
    fi

    file="$(module_path "$module")"
    if [ ! -f "$file" ]; then
      missing+=("$module -> $file")
      continue
    fi

    while IFS= read -r imported; do
      case "$imported" in
        Mathlib*) mathlib_offenders+=("$module imports $imported") ;;
        LeanProofs*) queue+=("$imported") ;;
      esac
    done < <(grep -E '^import ' "$file" | awk '{print $2}')
  done

  if [ "$boundary" = "core" ]; then
    core_count=${#seen[@]}
  else
    application_count=${#seen[@]}
  fi

  if [ ${#missing[@]} -gt 0 ]; then
    echo "FAIL: modules in $target closure with no source file:" >&2
    printf '  %s\n' "${missing[@]}" >&2
    status=2
  fi
  if [ ${#mathlib_offenders[@]} -gt 0 ]; then
    echo "FAIL: $target closure imports Mathlib:" >&2
    printf '  %s\n' "${mathlib_offenders[@]}" >&2
    status=3
  fi
  if [ ${#p25_offenders[@]} -gt 0 ]; then
    echo "FAIL: P25 escaped its explicit Mathlib island through $target:" >&2
    printf '  %s\n' "${p25_offenders[@]}" >&2
    status=4
  fi
  if [ ${#boundary_offenders[@]} -gt 0 ]; then
    echo "FAIL: $target crossed its declared custody boundary:" >&2
    printf '  %s\n' "${boundary_offenders[@]}" >&2
    status=5
  fi
}

audit_target ViewSemantics core
audit_target ViewSemanticsApplications application

custody_fail=0
while IFS= read -r file; do
  if ! grep -q 'Custody-Class: UNRATIFIED-CANDIDATE' "$file"; then
    echo "FAIL: candidate module lacks UNRATIFIED-CANDIDATE custody: $file" >&2
    custody_fail=1
  fi
done < <(find LeanProofs/ViewSemantics -type f -name '*.lean' -print; \
  printf '%s\n' LeanProofs/ViewSemantics.lean)

if [ "$custody_fail" -ne 0 ]; then status=6; fi

for source in \
  LeanProofs/Scratch/BindingSourceAblation.lean \
  LeanProofs/Scratch/NoSilentProjection.lean
do
  if ! grep -qE '^[[:space:]]*Custody-Class:[[:space:]]*SCRATCH[[:space:]]*$' "$source"; then
    echo "FAIL: allowlisted application source lacks exact SCRATCH custody: $source" >&2
    status=7
  fi
done

if [ "$status" -ne 0 ]; then exit "$status"; fi

echo "PASS — ViewSemantics core ($core_count modules) and applications ($application_count modules) are Mathlib-free and custody-separated; P25 remains isolated"
