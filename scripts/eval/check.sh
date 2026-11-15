#!/usr/bin/env bash
# Check one evaluation file under a build-admission slot and record its cost.
#
#   scripts/eval/check.sh <lane> <path/File.lean> [extra lean args...]
#
# Admission: at most EVAL_SLOTS (default 2) Lean checks run at once on this machine, each capped
# at EVAL_MEM MB (default 5000) with LEAN_NUM_THREADS=1; a check waits for a free slot. Each run
# appends one JSON line to EVAL_RECEIPTS (default ~/eval-receipts.jsonl): lane, file, exit code,
# wall time, peak RSS (KB) and the Lean profiler's cumulative times (elaboration, tactic
# execution, type checking = kernel). The full output is kept in ~/eval-logs/.
set -euo pipefail
lane="$1"; file="$2"; shift 2
repo="$(cd "$(dirname "$0")/../.." && pwd)"
slots="${EVAL_SLOTS:-2}"; mem="${EVAL_MEM:-5000}"
mkdir -p "$HOME/eval-slots" "$HOME/eval-logs"
stamp="$(date -u +%Y%m%dT%H%M%S)-$lane-$(basename "$file" .lean)"
log="$HOME/eval-logs/$stamp.log"
cd "$repo"
[ -f "$HOME/env.sh" ] && source "$HOME/env.sh"
export LEAN_NUM_THREADS=1
while true; do
  for i in $(seq 1 "$slots"); do
    exec {fd}>"$HOME/eval-slots/$i.lock"
    if flock -n "$fd"; then
      set +e
      /usr/bin/time -v -o "$log.time" lake env lean -M "$mem" -Dprofiler=true -Dprofiler.threshold=100000 "$@" "$file" > "$log" 2>&1
      code=$?
      set -e
      flock -u "$fd"
      wall=$(awk -F': ' '/Elapsed \(wall clock\)/{print $2}' "$log.time")
      rss=$(awk -F': ' '/Maximum resident set size/{print $2}' "$log.time")
      prof=$(grep -E '^\s+[a-z].* [0-9.]+(ms|s)$' "$log" | sed -E 's/^\s+//' | tr '\n' ';' | sed 's/"/ /g' || true)
      printf '{"lane":"%s","file":"%s","exit":%d,"wall":"%s","peak_rss_kb":%s,"profile":"%s","log":"%s"}\n' \
        "$lane" "$file" "$code" "$wall" "${rss:-0}" "$prof" "$log" >> "${EVAL_RECEIPTS:-$HOME/eval-receipts.jsonl}"
      cat "$log"
      echo "[check] exit=$code wall=$wall peak_rss_kb=$rss log=$log"
      exit "$code"
    fi
  done
  sleep 5
done
