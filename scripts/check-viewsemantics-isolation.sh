#!/usr/bin/env bash
# ViewSemantics custody/isolation gate.
#
# The stable and terminal-evidence roots are Mathlib-free. Every local module in
# the stable closure must be STABLE-SURFACE; the evidence closure may additionally
# reach PUBLIC-EVIDENCE. The P25 adapter remains behind the explicit non-default
# ViewSemanticsEvidenceMathlib island.

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$REPO_ROOT"

module_path() { printf '%s.lean\n' "${1//./\/}"; }

imports_of() {
  awk '
    /^[[:space:]]*import[[:space:]]+/ {
      for (i = 2; i <= NF; i++) {
        if ($i ~ /^--/) break
        print $i
      }
    }
  ' "$1"
}

target_roots() {
  local target="$1"
  awk -v target="$target" '
    /^\[\[lean_lib\]\]/ { name = ""; collecting = 0 }
    /^[[:space:]]*name[[:space:]]*=/ {
      value = $0
      sub(/^[^"]*"/, "", value)
      sub(/".*$/, "", value)
      name = value
    }
    name == target && /^[[:space:]]*roots[[:space:]]*=/ { collecting = 1 }
    name == target && collecting {
      line = $0
      while (match(line, /"[^"]+"/)) {
        print substr(line, RSTART + 1, RLENGTH - 2)
        line = substr(line, RSTART + RLENGTH)
      }
      if ($0 ~ /\]/) collecting = 0
    }
  ' lakefile.toml
}

role_of() {
  local file="$1"
  sed -n '1,40p' "$file" |
    grep -m1 -E '^[[:space:]]*Surface-Role:[[:space:]]*' |
    sed -E 's/^[[:space:]]*Surface-Role:[[:space:]]*//; s/[[:space:]]+$//'
}

status=0
core_count=0
evidence_count=0

audit_target() {
  local target="$1"
  local boundary="$2"
  mapfile -t roots < <(target_roots "$target")
  if [ "${#roots[@]}" -eq 0 ]; then
    echo "FAIL: no roots found for lean_lib $target" >&2
    status=1
    return
  fi

  local -A seen=()
  local -a queue=("${roots[@]}")
  local -a missing=()
  local -a mathlib=()
  local -a p25=()
  local -a role_offenders=()
  local module file imported role

  while [ "${#queue[@]}" -gt 0 ]; do
    module="${queue[0]}"
    queue=("${queue[@]:1}")
    [ -n "${seen[$module]:-}" ] && continue
    seen["$module"]=1

    case "$module" in
      LeanProofs.Paper25EpistemicBorderControl|LeanProofs.ViewSemantics.P25Adapter|LeanProofs.ViewSemantics.EvidenceMathlib)
        p25+=("$module")
        ;;
    esac

    file="$(module_path "$module")"
    if [ ! -f "$file" ]; then
      missing+=("$module -> $file")
      continue
    fi

    role="$(role_of "$file" || true)"
    if [ "$boundary" = "stable" ]; then
      if [ "$role" != "STABLE-SURFACE" ]; then
        role_offenders+=("$module (${role:-missing role})")
      fi
    else
      case "$role" in
        STABLE-SURFACE|PUBLIC-EVIDENCE) ;;
        *) role_offenders+=("$module (${role:-missing role})") ;;
      esac
    fi

    while IFS= read -r imported; do
      case "$imported" in
        Mathlib|Mathlib.*) mathlib+=("$module imports $imported") ;;
        LeanProofs.Scratch|LeanProofs.Scratch.*)
          role_offenders+=("$module imports legacy $imported")
          ;;
        LeanProofs|LeanProofs.*) queue+=("$imported") ;;
      esac
    done < <(imports_of "$file")
  done

  if [ "$boundary" = "stable" ]; then
    core_count="${#seen[@]}"
  else
    evidence_count="${#seen[@]}"
  fi

  if [ "${#missing[@]}" -gt 0 ]; then
    echo "FAIL: $target reaches missing sources:" >&2
    printf '  %s\n' "${missing[@]}" >&2
    status=2
  fi
  if [ "${#mathlib[@]}" -gt 0 ]; then
    echo "FAIL: $target closure imports Mathlib:" >&2
    printf '  %s\n' "${mathlib[@]}" >&2
    status=3
  fi
  if [ "${#p25[@]}" -gt 0 ]; then
    echo "FAIL: P25 escaped its explicit island through $target:" >&2
    printf '  %s\n' "${p25[@]}" >&2
    status=4
  fi
  if [ "${#role_offenders[@]}" -gt 0 ]; then
    echo "FAIL: $target crossed its Surface-Role boundary:" >&2
    printf '  %s\n' "${role_offenders[@]}" >&2
    status=5
  fi
}

audit_target ViewSemantics stable
audit_target ViewSemanticsEvidence evidence

mapfile -t island_roots < <(target_roots ViewSemanticsEvidenceMathlib)
if [ "${#island_roots[@]}" -ne 1 ] ||
   [ "${island_roots[0]:-}" != "LeanProofs.ViewSemantics.EvidenceMathlib" ]; then
  echo "FAIL: ViewSemanticsEvidenceMathlib must own exactly EvidenceMathlib" >&2
  status=6
fi
if [ "$(role_of LeanProofs/ViewSemantics/EvidenceMathlib.lean || true)" != "PUBLIC-EVIDENCE" ]; then
  echo "FAIL: EvidenceMathlib root must be terminal PUBLIC-EVIDENCE" >&2
  status=6
fi

default_targets="$(awk '
  /^defaultTargets[[:space:]]*=/ { capture = 1 }
  capture { print }
  capture && /\]/ { exit }
' lakefile.toml)"
for target in ViewSemantics ViewSemanticsEvidence; do
  if ! grep -Fq "\"$target\"" <<<"$default_targets"; then
    echo "FAIL: $target must remain default-built" >&2
    status=7
  fi
done
if grep -Fq '"ViewSemanticsEvidenceMathlib"' <<<"$default_targets"; then
  echo "FAIL: ViewSemanticsEvidenceMathlib must remain an explicit island" >&2
  status=7
fi

if [ "$status" -ne 0 ]; then exit "$status"; fi

echo "PASS — ViewSemantics stable ($core_count modules) and public evidence ($evidence_count modules) are Mathlib-free and role-separated; P25 remains isolated"
