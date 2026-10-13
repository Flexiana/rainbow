#!/usr/bin/env bash
set -euo pipefail

pinned_commit="c5ea00351c28e24afc9f0f84379aa41082b1188f"
lake_command="${RAINBOW_LEAN_BIN:+${RAINBOW_LEAN_BIN}/lake}"
lake_command="${lake_command:-lake}"
usage="usage: export-mathlib-statements.sh MATHLIB_CHECKOUT OUTPUT.edn NAME...\n       export-mathlib-statements.sh MATHLIB_CHECKOUT OUTPUT.edn --names-file FILE"
mathlib_dir="${1:?$usage}"
output_path="${2:?$usage}"
shift 2

requested_names=()
if [ "${1:-}" = "--names-file" ]; then
  if [ "$#" -ne 2 ] || [ ! -r "$2" ]; then
    printf '%b\n' "$usage" >&2
    exit 1
  fi
  while IFS=$'\t' read -r name module || [ -n "$name" ]; do
    if [ -z "$name" ]; then
      echo "blank declaration name in $2" >&2
      exit 1
    fi
    if [ -n "${module:-}" ]; then
      requested_names+=("${name}|${module}")
    else
      requested_names+=("$name")
    fi
  done < "$2"
else
  requested_names=("$@")
fi

if [ "${#requested_names[@]}" -eq 0 ]; then
  echo "at least one declaration name is required" >&2
  exit 1
fi

script_dir="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
rainbow_dir="$(dirname -- "$script_dir")"
actual_commit="$(git -C "$mathlib_dir" rev-parse HEAD)"

if [ "$actual_commit" != "$pinned_commit" ]; then
  echo "expected Mathlib commit $pinned_commit, found $actual_commit" >&2
  exit 1
fi

if ! git -C "$mathlib_dir" diff --quiet || \
   ! git -C "$mathlib_dir" diff --cached --quiet; then
  echo "Mathlib checkout has tracked changes; refusing ambiguous provenance" >&2
  exit 1
fi

partial_path="${output_path}.partial"
manifest_path="${output_path}.modules.tsv"
requests_path="${output_path}.requests.tsv"
olean_root="$mathlib_dir/.lake/build/lib/lean/Mathlib"

if [ ! -d "$olean_root" ]; then
  echo "missing compiled Mathlib cache at $olean_root" >&2
  exit 1
fi

while IFS= read -r olean_path; do
  relative_path="${olean_path#"$mathlib_dir/.lake/build/lib/lean/"}"
  module_name="${relative_path%.olean}"
  module_name="${module_name//\//.}"
  printf '%s\t%s\n' "$module_name" "$olean_path"
done < <(find "$olean_root" -type f -name '*.olean' | LC_ALL=C sort) > "$manifest_path"

: > "$requests_path"
for request in "${requested_names[@]}"; do
  if [[ "$request" == *"|"* ]]; then
    printf '%s\t%s\n' "${request%%|*}" "${request#*|}" >> "$requests_path"
  else
    printf '%s\n' "$request" >> "$requests_path"
  fi
done

if ! (
  cd "$mathlib_dir"
  "$lake_command" env lean --run \
    "$rainbow_dir/foreign/lean/MathlibStatements.lean" \
    "$manifest_path" "$requests_path"
) > "$partial_path"; then
  cat "$partial_path" >&2
  exit 1
fi

mv "$partial_path" "$output_path"
echo "$output_path"
