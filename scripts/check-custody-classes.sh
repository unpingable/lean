#!/usr/bin/env bash
# Whole-tree v13 custody gate.
#
# The public repository has one live Lean custody class: PUBLIC-SHIPPED.
# Surface-Role distinguishes stable substrate, terminal public evidence, and
# the repository aggregate. Incubation belongs in the sibling skunkworks repo.
#
# public-custody.tsv registers every retained Lean source and its exact
# stable-surface owners. stable-surfaces.tsv registers every stable root.
# Filesystem enumeration includes untracked sources; only Git metadata and
# Lake dependency/build directories are pruned.

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$REPO_ROOT"

PUBLIC_REGISTRY="scripts/public-custody.tsv"
STABLE_REGISTRY="scripts/stable-surfaces.tsv"
LAKEFILE="lakefile.toml"

for required in "$PUBLIC_REGISTRY" "$STABLE_REGISTRY" "$LAKEFILE"; do
  if [ ! -f "$required" ]; then
    echo "FAIL: required custody source of truth is missing: $required" >&2
    exit 1
  fi
done

fail=0

module_path() {
  printf '%s.lean\n' "${1//./\/}"
}

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

canonical_owners() {
  local owners="$1"
  if [ -z "$owners" ] || [ "$owners" = "-" ]; then
    printf '%s\n' "-"
    return
  fi
  tr ',' '\n' <<<"$owners" | sed '/^$/d' | LC_ALL=C sort -u | paste -sd ',' -
}

target_has_root() {
  local target="$1"
  local root="$2"
  awk -v target="$target" -v root="$root" '
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
        value = substr(line, RSTART + 1, RLENGTH - 2)
        if (value == root) found = 1
        line = substr(line, RSTART + RLENGTH)
      }
      if ($0 ~ /\]/) collecting = 0
    }
    END { exit(found ? 0 : 1) }
  ' "$LAKEFILE"
}

declare -A EXPECT_ROLE=()
declare -A EXPECT_OWNERS=()
registry_count=0

while IFS=$'\t' read -r path role owners extra; do
  [[ -z "${path:-}" || "$path" == \#* ]] && continue
  if [ -n "${extra:-}" ] || [ -z "${role:-}" ] || [ -z "${owners:-}" ]; then
    echo "FAIL: malformed row in $PUBLIC_REGISTRY: $path" >&2
    fail=1
    continue
  fi
  if [[ "$path" = /* || "$path" == ./* || "$path" == *"/../"* ||
        "$path" == ../* || "$path" == ".lake/"* ]]; then
    echo "FAIL: non-canonical path in $PUBLIC_REGISTRY: $path" >&2
    fail=1
  fi
  if [ -n "${EXPECT_ROLE[$path]:-}" ]; then
    echo "FAIL: duplicate path in $PUBLIC_REGISTRY: $path" >&2
    fail=1
    continue
  fi

  case "$role" in
    STABLE-SURFACE)
      if [ "$owners" = "-" ]; then
        echo "FAIL: stable row has no stable owner: $path" >&2
        fail=1
      fi
      ;;
    PUBLIC-EVIDENCE|REPOSITORY-AGGREGATE)
      if [ "$owners" != "-" ]; then
        echo "FAIL: non-stable row claims stable ownership: $path -> $owners" >&2
        fail=1
      fi
      ;;
    *)
      echo "FAIL: unrecognized Surface-Role: $path -> $role" >&2
      fail=1
      ;;
  esac

  canonical="$(canonical_owners "$owners")"
  if [ "$canonical" != "$owners" ]; then
    echo "FAIL: owner list is not sorted and unique: $path -> $owners" >&2
    echo "      expected: $canonical" >&2
    fail=1
  fi

  EXPECT_ROLE["$path"]="$role"
  EXPECT_OWNERS["$path"]="$owners"
  registry_count=$((registry_count + 1))
done < "$PUBLIC_REGISTRY"

mapfile -t ACTUAL_FILES < <(
  find . \
    \( -type d \( -name .git -o -name .lake -o -name lake-packages \) -prune \) -o \
    -type f -name '*.lean' -print |
    sed 's#^\./##' |
    LC_ALL=C sort
)

declare -A ACTUAL_SET=()
class_count=0
stable_role_count=0
evidence_role_count=0
aggregate_role_count=0

for path in "${ACTUAL_FILES[@]}"; do
  ACTUAL_SET["$path"]=1

  if [[ "$path" == Scratch/* || "$path" == */Scratch/* ]]; then
    echo "FAIL: legacy Scratch path remains: $path" >&2
    fail=1
  fi
  if [ -z "${EXPECT_ROLE[$path]:-}" ]; then
    echo "FAIL: unregistered Lean source: $path" >&2
    fail=1
  fi

  mapfile -t class_markers < <(
    grep -nE '^[[:space:]]*Custody-Class:[[:space:]]*' "$path" || true
  )
  declared_class=""
  if [ "${#class_markers[@]}" -ne 1 ]; then
    echo "FAIL: $path has ${#class_markers[@]} Custody-Class markers; expected 1" >&2
    fail=1
  else
    class_line="${class_markers[0]%%:*}"
    declared_class="$(sed -E \
      's/^[[:space:]]*Custody-Class:[[:space:]]*//; s/[[:space:]]+$//' \
      <<<"${class_markers[0]#*:}")"
    if [ "$class_line" -gt 40 ]; then
      echo "FAIL: $path Custody-Class is below the 40-line header fence" >&2
      fail=1
    fi
    if [ "$declared_class" != "PUBLIC-SHIPPED" ]; then
      echo "FAIL: $path declares legacy/unrecognized custody '$declared_class'" >&2
      fail=1
    else
      class_count=$((class_count + 1))
    fi
  fi

  mapfile -t role_markers < <(
    grep -nE '^[[:space:]]*Surface-Role:[[:space:]]*' "$path" || true
  )
  declared_role=""
  if [ "${#role_markers[@]}" -ne 1 ]; then
    echo "FAIL: $path has ${#role_markers[@]} Surface-Role markers; expected 1" >&2
    fail=1
  else
    role_line="${role_markers[0]%%:*}"
    declared_role="$(sed -E \
      's/^[[:space:]]*Surface-Role:[[:space:]]*//; s/[[:space:]]+$//' \
      <<<"${role_markers[0]#*:}")"
    if [ "$role_line" -gt 40 ]; then
      echo "FAIL: $path Surface-Role is below the 40-line header fence" >&2
      fail=1
    fi
    case "$declared_role" in
      STABLE-SURFACE) stable_role_count=$((stable_role_count + 1)) ;;
      PUBLIC-EVIDENCE) evidence_role_count=$((evidence_role_count + 1)) ;;
      REPOSITORY-AGGREGATE) aggregate_role_count=$((aggregate_role_count + 1)) ;;
      *)
        echo "FAIL: $path declares unrecognized Surface-Role '$declared_role'" >&2
        fail=1
        ;;
    esac
  fi

  if [ -n "${EXPECT_ROLE[$path]:-}" ] &&
     [ "$declared_role" != "${EXPECT_ROLE[$path]}" ]; then
    echo "FAIL: $path role is '${declared_role:-<missing>}'" >&2
    echo "      registry requires '${EXPECT_ROLE[$path]}'" >&2
    fail=1
  fi

  while IFS= read -r imported; do
    if [[ "$imported" == LeanProofs.Scratch ||
          "$imported" == LeanProofs.Scratch.* ]]; then
      echo "FAIL: legacy Scratch import: $path imports $imported" >&2
      fail=1
    fi
  done < <(imports_of "$path")
done

for path in "${!EXPECT_ROLE[@]}"; do
  if [ -z "${ACTUAL_SET[$path]:-}" ]; then
    echo "FAIL: registered public source is missing: $path" >&2
    fail=1
  fi
done

declare -A SURFACE_TARGET=()
declare -A SURFACE_POLICY=()
declare -A KNOWN_SURFACE=()
declare -A SEEN_ROOT=()
declare -a ROOT_SURFACE=()
declare -a ROOT_MODULE=()
declare -a ROOT_POLICY=()
root_count=0

while IFS=$'\t' read -r surface target root policy extra; do
  [[ -z "${surface:-}" || "$surface" == \#* ]] && continue
  if [ -n "${extra:-}" ] || [ -z "${target:-}" ] ||
     [ -z "${root:-}" ] || [ -z "${policy:-}" ]; then
    echo "FAIL: malformed row in $STABLE_REGISTRY: $surface" >&2
    fail=1
    continue
  fi
  if [[ ! "$surface" =~ ^[a-z0-9][a-z0-9-]*$ ]]; then
    echo "FAIL: invalid stable surface identifier: $surface" >&2
    fail=1
  fi
  if [[ ! "$root" =~ ^LeanProofs([.][A-Za-z0-9_]+)*$ ]]; then
    echo "FAIL: invalid stable root module: $root" >&2
    fail=1
  fi
  if [ "$policy" != "mathlib-free" ]; then
    echo "FAIL: unsupported stable import policy '$policy' for $surface" >&2
    fail=1
  fi
  if [ -n "${SEEN_ROOT[$root]:-}" ]; then
    echo "FAIL: stable root registered more than once: $root" >&2
    fail=1
    continue
  fi
  if [ -n "${SURFACE_TARGET[$surface]:-}" ] &&
     { [ "${SURFACE_TARGET[$surface]}" != "$target" ] ||
       [ "${SURFACE_POLICY[$surface]}" != "$policy" ]; }; then
    echo "FAIL: surface $surface has inconsistent target or policy" >&2
    fail=1
  fi

  SURFACE_TARGET["$surface"]="$target"
  SURFACE_POLICY["$surface"]="$policy"
  KNOWN_SURFACE["$surface"]=1
  SEEN_ROOT["$root"]=1
  ROOT_SURFACE+=("$surface")
  ROOT_MODULE+=("$root")
  ROOT_POLICY+=("$policy")
  root_count=$((root_count + 1))

  if ! target_has_root "$target" "$root"; then
    echo "FAIL: Lake target $target does not own registered root $root" >&2
    fail=1
  fi
done < "$STABLE_REGISTRY"

for path in "${!EXPECT_ROLE[@]}"; do
  owners="${EXPECT_OWNERS[$path]}"
  [ "$owners" = "-" ] && continue
  IFS=',' read -r -a owner_list <<<"$owners"
  for surface in "${owner_list[@]}"; do
    if [ -z "${KNOWN_SURFACE[$surface]:-}" ]; then
      echo "FAIL: $path names unknown stable owner '$surface'" >&2
      fail=1
    fi
  done
done

declare -A REACHED_BY=()
declare -A SEEN_MODULE=()
declare -A MATHLIB_OFFENDER_SEEN=()

add_owner() {
  local path="$1"
  local surface="$2"
  local current="${REACHED_BY[$path]:-}"
  if [ -z "$current" ]; then
    REACHED_BY["$path"]="$surface"
  elif [[ ",$current," != *",$surface,"* ]]; then
    REACHED_BY["$path"]="$current,$surface"
  fi
}

for ((i = 0; i < root_count; i++)); do
  surface="${ROOT_SURFACE[$i]}"
  policy="${ROOT_POLICY[$i]}"
  queue=("${ROOT_MODULE[$i]}")

  while [ "${#queue[@]}" -gt 0 ]; do
    module="${queue[0]}"
    queue=("${queue[@]:1}")
    key="$surface|$module"
    [ -n "${SEEN_MODULE[$key]:-}" ] && continue
    SEEN_MODULE["$key"]=1

    path="$(module_path "$module")"
    if [ ! -f "$path" ]; then
      echo "FAIL: stable surface $surface reaches missing source: $module -> $path" >&2
      fail=1
      continue
    fi
    add_owner "$path" "$surface"

    while IFS= read -r imported; do
      case "$imported" in
        LeanProofs|LeanProofs.*)
          queue+=("$imported")
          ;;
        Mathlib|Mathlib.*)
          if [ "$policy" = "mathlib-free" ]; then
            offender="$surface|$module|$imported"
            if [ -z "${MATHLIB_OFFENDER_SEEN[$offender]:-}" ]; then
              echo "FAIL: Mathlib escaped into stable surface $surface:" >&2
              echo "      $module imports $imported" >&2
              MATHLIB_OFFENDER_SEEN["$offender"]=1
              fail=1
            fi
          fi
          ;;
      esac
    done < <(imports_of "$path")
  done
done

for path in "${!REACHED_BY[@]}"; do
  actual_owners="$(canonical_owners "${REACHED_BY[$path]}")"
  role="${EXPECT_ROLE[$path]:-<unregistered>}"
  if [ "$role" != "STABLE-SURFACE" ]; then
    echo "FAIL: stable closure reaches non-stable source: $path ($role)" >&2
    echo "      reached by: $actual_owners" >&2
    fail=1
  fi
done

for path in "${!EXPECT_ROLE[@]}"; do
  expected_owners="${EXPECT_OWNERS[$path]}"
  actual_owners="$(canonical_owners "${REACHED_BY[$path]:--}")"
  if [ "$actual_owners" != "$expected_owners" ]; then
    echo "FAIL: stable closure ownership drift for $path" >&2
    echo "      actual:   $actual_owners" >&2
    echo "      expected: $expected_owners" >&2
    fail=1
  fi
done

if [ "$fail" -ne 0 ]; then
  echo "FAIL: whole-tree custody classification does not close" >&2
  exit 1
fi

echo "PASS — whole-tree custody closes exactly"
echo "  Lean sources:          ${#ACTUAL_FILES[@]}"
echo "  PUBLIC-SHIPPED:        $class_count"
echo "  STABLE-SURFACE:        $stable_role_count"
echo "  PUBLIC-EVIDENCE:       $evidence_role_count"
echo "  REPOSITORY-AGGREGATE:  $aggregate_role_count"
echo "  stable roots:          $root_count"
echo "  stable ownerships:     ${#SEEN_MODULE[@]}"
