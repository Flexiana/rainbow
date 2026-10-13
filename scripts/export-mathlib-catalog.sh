#!/usr/bin/env bash
set -euo pipefail

pinned_commit="c5ea00351c28e24afc9f0f84379aa41082b1188f"
mathlib_dir="${1:?usage: export-mathlib-catalog.sh MATHLIB_CHECKOUT [OUTPUT.edn.gz]}"
output_path="${2:-/tmp/rainbow-mathlib-v4.30.0-catalog.edn.gz}"
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

if [ ! -f "$mathlib_dir/lake-manifest.json" ]; then
  echo "missing pinned Mathlib lake-manifest.json" >&2
  exit 1
fi

partial_path="${output_path}.partial"
manifest_path="${output_path}.modules.tsv"
olean_root="$mathlib_dir/.lake/build/lib/lean/Mathlib"
lane_count="${RAINBOW_MATHLIB_CATALOG_LANES:-2}"

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

if [ "$lane_count" != "1" ] && [ "$lane_count" != "2" ]; then
  echo "RAINBOW_MATHLIB_CATALOG_LANES must be 1 or 2" >&2
  exit 1
fi

if [ "$lane_count" = "1" ]; then
  if ! (
    cd "$mathlib_dir"
    lake env lean --run "$rainbow_dir/foreign/lean/MathlibOleanCatalog.lean" \
      "$manifest_path"
  ) | gzip -n > "$partial_path"; then
    gzip -dc "$partial_path" >&2 || true
    exit 1
  fi
else
  module_count="$(wc -l < "$manifest_path")"
  first_count="$(( (module_count + 1) / 2 ))"
  second_start="$(( first_count + 1 ))"
  first_manifest="${manifest_path}.0"
  second_manifest="${manifest_path}.1"
  first_output="${partial_path}.0.gz"
  second_output="${partial_path}.1.gz"
  sed -n "1,${first_count}p" "$manifest_path" > "$first_manifest"
  sed -n "${second_start},${module_count}p" "$manifest_path" > "$second_manifest"

  (
    cd "$mathlib_dir"
    lake env lean --run "$rainbow_dir/foreign/lean/MathlibOleanCatalog.lean" \
      "$first_manifest"
  ) | gzip -n > "$first_output" &
  first_pid="$!"
  (
    cd "$mathlib_dir"
    lake env lean --run "$rainbow_dir/foreign/lean/MathlibOleanCatalog.lean" \
      "$second_manifest" --no-header
  ) | gzip -n > "$second_output" &
  second_pid="$!"

  first_status=0
  second_status=0
  wait "$first_pid" || first_status="$?"
  wait "$second_pid" || second_status="$?"
  if [ "$first_status" != "0" ] || [ "$second_status" != "0" ]; then
    echo "catalog shard failure: first=$first_status second=$second_status" >&2
    exit 1
  fi
  cat "$first_output" "$second_output" > "$partial_path"
fi

mv "$partial_path" "$output_path"
echo "$output_path"
