#!/usr/bin/env bash
# Run the test suite as a sequence of namespace-scoped JVMs.
#
# A single whole-suite JVM does not fit on every machine: on the development box
# it reached ~12.7GB RSS and was terminated by the OS twice, each time after
# hundreds of namespaces had already passed, and each time WITHOUT writing a
# summary. An all-or-nothing run that vanishes when the process is killed tells
# you nothing about the hundreds of namespaces that did pass, and a missing
# summary is indistinguishable from a hang.
#
# So: chunk by namespace, and make every chunk account for itself.
# The 1.5.0 release run exhausted a 5GB heap with twenty retained proof
# environments. Default to five; callers may explicitly choose another size.
#
#   * each chunk writes its own summary line to the results file the moment it
#     finishes, so a chunk that dies is VISIBLY MISSING rather than silent;
#   * a chunk that exits without writing that line is reported as TERMINATED,
#     loudly and distinctly from a test failure, because resource termination and
#     a failing assertion demand completely different responses;
#   * this script's JVMs are killed between chunks, scoped to this working
#     directory, so a concurrent agent's JVMs are never touched.
#
# usage: scripts/run-suite-chunked.sh [CHUNK_SIZE] [RESULTS_FILE]
set -uo pipefail

chunk_size="${1:-5}"
results="${2:-target/suite-chunks.tsv}"

# Resume support. A run stopped part-way -- by the operator, by the OS, or to run
# one part on its own -- should not have to repeat the chunks that already
# passed. RAINBOW_START_CHUNK=5 skips straight to chunk 5 using the same chunk
# numbering, so chunk 5 means the same configured namespaces it meant last time.
start_chunk="${RAINBOW_START_CHUNK:-1}"
for value in "$chunk_size" "$start_chunk"; do
  if [[ ! "$value" =~ ^[1-9][0-9]{0,8}$ ]]; then
    echo "chunk size and start chunk must be integers from 1 to 999999999" >&2
    exit 2
  fi
done
script_dir="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
rainbow_dir="$(dirname -- "$script_dir")"
cd "$rainbow_dir"

# free pages below which we wait rather than start a chunk; a chunk started with
# no headroom is a chunk that will be terminated
min_free_pages="${RAINBOW_MIN_FREE_PAGES:-98304}"   # 1.5GB at 16KiB pages
wait_limit_seconds="${RAINBOW_HEADROOM_WAIT:-600}"

# Per-chunk logs are named after the RESULTS FILE, not a fixed path. Two runs of
# this script share target/, and a fixed `suite-chunk-N.log` means a second run
# overwrites -- or a caller clearing stale logs deletes -- the log a first run is
# still writing. That produced a spurious TERMINATED verdict once: the chunk
# passed, its log was removed underneath it, and the summary line could not be
# found. Deriving the name from `results` makes concurrent runs independent.
log_prefix="${results%.*}"

# PIDs this script started itself, and only those.
#
# This used to kill by working-directory pattern. That is safe against a
# CONCURRENT AGENT -- their JVMs live under a different directory -- but not
# against a concurrent run of your own: a measurement JVM started from this same
# repo matches the pattern and dies. That happened, silently, the first time the
# one-JVM-at-a-time convention was relaxed. Scope by PID and the question of who
# else is running stops mattering.
started_pids=()

remember_pid() { started_pids+=("$1"); }

kill_own_jvms() {
  local pid
  for pid in "${started_pids[@]:-}"; do
    [ -n "$pid" ] || continue
    # the lein launcher spawns a java child; take the tree, but only OUR tree
    pkill -9 -P "$pid" 2>/dev/null || true
    kill -9 "$pid" 2>/dev/null || true
  done
  started_pids=()
}

free_pages() {
  vm_stat 2>/dev/null | awk '/Pages free/ {gsub(/\./,"",$3); print $3; exit}' \
    || echo "$min_free_pages"
}

await_headroom() {
  local waited=0
  while [ "$(free_pages)" -lt "$min_free_pages" ]; do
    if [ "$waited" -ge "$wait_limit_seconds" ]; then
      echo "warning: proceeding without headroom after ${waited}s" >&2
      return 0
    fi
    sleep 15
    waited=$((waited + 15))
  done
}

# rainbow.foo-bar-test from test/rainbow/foo_bar_test.clj
# RAINBOW_NS_FILTER restricts the run to matching namespaces, which is how this
# script is smoke-tested without paying for a whole suite
namespaces() {
  find test -name '*_test.clj' -type f \
    | sed -e 's|^test/||' -e 's|\.clj$||' -e 's|/|.|g' -e 's|_|-|g' \
    | { if [ -n "${RAINBOW_NS_FILTER:-}" ]; then grep -E "$RAINBOW_NS_FILTER"; else cat; fi; } \
    | sort
}

all_namespaces=()
while IFS= read -r namespace; do
  all_namespaces+=("$namespace")
done < <(namespaces)

total="${#all_namespaces[@]}"
if [ "$total" -eq 0 ]; then
  echo "no test namespaces found under test/" >&2
  exit 1
fi
last_chunk=$(( (total + chunk_size - 1) / chunk_size ))
if [ "$start_chunk" -gt "$last_chunk" ]; then
  echo "start chunk $start_chunk exceeds the $last_chunk available chunks; nothing would run" >&2
  exit 2
fi
mkdir -p "$(dirname -- "$results")"
: > "$results"

if [ "$start_chunk" -gt 1 ]; then
  echo "running $total namespaces in chunks of $chunk_size, RESUMING at chunk $start_chunk"
else
  echo "running $total namespaces in chunks of $chunk_size"
fi
printf 'chunk\tstatus\ttests\tassertions\tfailures\terrors\tnamespaces\tseconds\n' >> "$results"

chunk_index=0
terminated=0
failed=0
sum_tests=0
sum_assertions=0
sum_failures=0
sum_errors=0

for ((start = 0; start < total; start += chunk_size)); do
  chunk_index=$((chunk_index + 1))
  if [ "$chunk_index" -lt "$start_chunk" ]; then
    continue
  fi
  chunk=("${all_namespaces[@]:start:chunk_size}")
  log="${log_prefix}-chunk-${chunk_index}.log"

  await_headroom
  kill_own_jvms

  # Timestamp each per-namespace header line as it streams, so a slow
  # namespace is visible from the log alone (the namespace-11 lesson:
  # an hour of profiling that one wall-time column would have answered).
  # The filter runs inside a pipefail subshell so lein's exit code is
  # preserved -- a bare pipe here would substitute the filter's exit for
  # the suite's, the exact defect gate invocations had on 2026-09-06 --
  # and waiting on the subshell means the pipeline (and the log) is
  # complete before the summary lines below are grepped.
  chunk_started=$(date +%s)
  ( set -o pipefail
    lein test "${chunk[@]}" < /dev/null 2>&1 \
      | perl -MPOSIX -pe \
        'BEGIN { $| = 1 }
         $_ = strftime("[%H:%M:%S] ", localtime) . $_
           if /^lein test (:only )?rainbow\./;' > "$log" ) &
  chunk_pid=$!
  remember_pid "$chunk_pid"
  wait "$chunk_pid"
  exit_code=$?
  chunk_seconds=$(( $(date +%s) - chunk_started ))

  # `lein test` prints "Ran N tests containing M assertions." then
  # "X failures, Y errors."; absence of the first is the termination signal
  ran_line="$(grep -E '^Ran [0-9]+ tests containing [0-9]+ assertions' "$log" | tail -1)"
  tally_line="$(grep -E '^[0-9]+ failures, [0-9]+ errors' "$log" | tail -1)"

  if [ -z "$ran_line" ] || [ -z "$tally_line" ]; then
    terminated=$((terminated + 1))
    printf '%d\tTERMINATED\t-\t-\t-\t-\t%d\t%d\n' \
      "$chunk_index" "${#chunk[@]}" "$chunk_seconds" >> "$results"
    echo "chunk $chunk_index TERMINATED (exit $exit_code, no summary written): $log" >&2
    continue
  fi

  tests="$(sed -E 's/^Ran ([0-9]+) tests.*/\1/' <<< "$ran_line")"
  assertions="$(sed -E 's/.*containing ([0-9]+) assertions.*/\1/' <<< "$ran_line")"
  failures="$(sed -E 's/^([0-9]+) failures.*/\1/' <<< "$tally_line")"
  errors="$(sed -E 's/.*, ([0-9]+) errors.*/\1/' <<< "$tally_line")"

  sum_tests=$((sum_tests + tests))
  sum_assertions=$((sum_assertions + assertions))
  sum_failures=$((sum_failures + failures))
  sum_errors=$((sum_errors + errors))

  if [ "$exit_code" -eq 0 ] && [ "$tests" -gt 0 ] && [ "$failures" -eq 0 ] && [ "$errors" -eq 0 ]; then
    status=PASS
  else
    status=FAIL
    failed=$((failed + 1))
  fi

  printf '%d\t%s\t%d\t%d\t%d\t%d\t%d\t%d\n' \
    "$chunk_index" "$status" "$tests" "$assertions" "$failures" "$errors" \
    "${#chunk[@]}" "$chunk_seconds" >> "$results"
  echo "chunk $chunk_index $status: exit $exit_code, $tests tests, $assertions assertions, $failures failures, $errors errors, ${chunk_seconds}s"
done

kill_own_jvms

echo
echo "chunks: $chunk_index   failed: $failed   terminated: $terminated"
echo "totals: $sum_tests tests, $sum_assertions assertions, $sum_failures failures, $sum_errors errors"
echo "per-chunk results: $results"

if [ "$terminated" -gt 0 ]; then
  echo "SUITE INCOMPLETE: $terminated chunk(s) were terminated without writing a summary." >&2
  echo "This is resource termination, not a test failure; the chunks above are unverified." >&2
  exit 2
fi

if [ "$failed" -gt 0 ]; then
  echo "SUITE FAILED: $failed chunk(s) reported failures or errors." >&2
  exit 1
fi

echo "SUITE PASSED"
