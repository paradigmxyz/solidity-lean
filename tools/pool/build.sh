#!/usr/bin/env bash
# Build or check solidity-lean on a worker, reporting wall time and peak memory.
#
#   tools/pool/build.sh [--dir DIR] [--threads N] [--report FILE] ci
#   tools/pool/build.sh ... ci-gen          # also the generated Uniswap V2 steps (needs --with-rust)
#   tools/pool/build.sh ... audit           # CI's axiom audit and proof checks (after a ci-gen build)
#   tools/pool/build.sh ... Mod.Name [...]  # lake build of one or more targets or modules
#   tools/pool/build.sh ... --check path/To/File.lean   # lake env lean on one file
#
# ci and ci-gen run the build commands of .github/workflows/refinement.yml at the checked-out
# commit (tools/pool/ci_steps.py reads them), in its order and with its -KleanMemory caps, but
# with LEAN_NUM_THREADS=N (default: one per CPU, at most one per 5 GB of RAM) instead of 2.
# Each step prints its wall time and the largest single process's peak RSS; the summary adds
# the machine-wide peak of used memory. Results are appended as JSON lines to FILE (default
# DIR/.lake/pool-report.jsonl). Exits non-zero on the first failing step.
source "$(dirname "${BASH_SOURCE[0]}")/common.sh"
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

dir="" threads="" report="" check="" mem="${POOL_LEAN_MEMORY:-6000}" args=()
while (( $# )); do
  case "$1" in
    --dir) dir="$2"; shift 2 ;;
    --threads) threads="$2"; shift 2 ;;
    --report) report="$2"; shift 2 ;;
    --check) check="$2"; shift 2 ;;
    --memory) mem="$2"; shift 2 ;;
    -h|--help) sed -n '2,16p' "$0"; exit 0 ;;
    *) args+=("$1"); shift ;;
  esac
done
dir="${dir:-$POOL_ROOT/solidity-lean}"
threads="${threads:-$(pool_default_threads)}"
[[ -d "$dir/.git" ]] || pool_die "$dir is not a checkout (run bootstrap.sh first)"
cd "$dir"
mkdir -p .lake
report="${report:-$dir/.lake/pool-report.jsonl}"
export LEAN_NUM_THREADS="$threads"
sha="$(git rev-parse HEAD)"
host="$(hostname)"

peakfile="$(mktemp)"; echo 0 > "$peakfile"
pool_mem_sampler "$peakfile" & sampler=$!
trap 'kill $sampler 2>/dev/null || true; rm -f "$peakfile"' EXIT

total_start=$(date +%s)
steps_json=()
run_step() {  # name, script
  local name="$1" script="$2" start wall rc rss
  pool_log "step: $name"
  start=$(date +%s.%N)
  set +e
  /usr/bin/time -f '%M' -o .lake/pool-step.time bash -euo pipefail -c "$script"
  rc=$?
  set -e
  wall=$(awk -v s="$start" -v e="$(date +%s.%N)" 'BEGIN {printf "%.0f", e-s}')
  rss="$(tail -n1 .lake/pool-step.time 2>/dev/null || echo 0)"
  [[ "$rss" =~ ^[0-9]+$ ]] || rss=0
  pool_log "step: $name: exit $rc, ${wall}s, largest process $(pool_gib "$rss") GiB"
  steps_json+=("$(python3 -c 'import json,sys; print(json.dumps({"step":sys.argv[1],"exit":int(sys.argv[2]),"wall_s":int(sys.argv[3]),"max_rss_kib":int(sys.argv[4])}))' "$name" "$rc" "$wall" "$rss")")
  return "$rc"
}

finish() {
  local rc="$1" total peak
  total=$(( $(date +%s) - total_start ))
  peak="$(cat "$peakfile")"
  pool_log "done: exit $rc, ${total}s wall, machine-wide peak used memory $(pool_gib "$peak") GiB, LEAN_NUM_THREADS=$threads on $(nproc) CPUs / $(pool_mem_gb) GB"
  local IFS=,
  printf '{"sha":"%s","host":"%s","target":"%s","threads":%s,"cpus":%s,"mem_gb":%s,"exit":%s,"wall_s":%s,"peak_used_kib":%s,"steps":[%s]}\n' \
    "$sha" "$host" "${label//\"/}" "$threads" "$(nproc)" "$(pool_mem_gb)" "$rc" "$total" "$peak" "${steps_json[*]}" >> "$report"
  exit "$rc"
}

rc=0
if [[ -n "$check" ]]; then
  label="check $check"
  run_step "lake env lean $check" "lake env lean -M $mem '$check'" || rc=$?
  finish "$rc"
fi
(( ${#args[@]} )) || pool_die "nothing to build: give ci, ci-gen, audit, targets, or --check FILE"
case "${args[0]}" in
  ci|ci-gen|audit)
    label="${args[0]}"
    plan="$(python3 "$here/ci_steps.py" .github/workflows/refinement.yml "${args[0]}")"
    name="" body=""
    while IFS= read -r line; do
      if [[ "$line" == "@@step "* ]]; then
        if [[ -n "$name" ]]; then run_step "$name" "$body" || { rc=$?; finish "$rc"; }; fi
        name="${line#@@step }"; body=""
      else
        body+="$line"$'\n'
      fi
    done <<< "$plan"
    if [[ -n "$name" ]]; then run_step "$name" "$body" || rc=$?; fi
    ;;
  *)
    label="${args[*]}"
    run_step "lake build ${args[*]}" "lake build -KleanMemory=$mem ${args[*]}" || rc=$?
    ;;
esac
finish "$rc"
