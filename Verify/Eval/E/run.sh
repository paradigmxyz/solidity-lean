#!/usr/bin/env bash
# Lane E runner (docs/eval/e.md): check one generated fixture under the shared admission slots of
# scripts/eval/check.sh, write its .olean, and append one JSON line with every metric to
# E_RESULTS (default ~/evalE/results.jsonl).
#
#   Verify/Eval/E/run.sh <fixture.lean> [olean-dir]
#
# LEAN_PATH puts ~/evalE/olean (Measure, Toy, Stats compiled by Verify/Eval/E/setup.sh) before the
# project's own paths, so fixtures need no lake build of the VerifyEval library.
set -euo pipefail
file="$1"; odir="${2:-$HOME/evalE/out}"
repo="$(cd "$(dirname "$0")/../../.." && pwd)"
slots="${EVAL_SLOTS:-2}"; mem="${EVAL_MEM:-5000}"
mkdir -p "$HOME/eval-slots" "$odir" "$HOME/evalE/logs"
name="$(basename "$file" .lean)"
log="$HOME/evalE/logs/$name.log"
results="${E_RESULTS:-$HOME/evalE/results.jsonl}"
cd "$repo"
[ -f "$HOME/env.sh" ] && source "$HOME/env.sh"
export LEAN_PATH="$HOME/evalE/olean:$(lake env printenv LEAN_PATH)"
export LEAN_NUM_THREADS=1
# E_NOSLOT=1 runs at once, outside the shared slots (one lane E check at a time, by the caller).
while true; do
  for i in $(seq 1 "$slots"); do
    if [ "${E_NOSLOT:-0}" = 1 ]; then exec {fd}>"$HOME/evalE/noslot.lock"; else exec {fd}>"$HOME/eval-slots/$i.lock"; fi
    if flock -n "$fd"; then
      set +e
      /usr/bin/time -v -o "$log.time" lean --root="$(cd "$(dirname "$file")" && pwd)" -M "$mem" -DmaxHeartbeats=1000000 -Dbackward.do.legacy=true -Dprofiler=true -Dprofiler.threshold=100000 \
        -o "$odir/$name.olean" "$file" > "$log" 2>&1
      code=$?
      set -e
      flock -u "$fd"
      python3 "$repo/Verify/Eval/E/parse.py" "$name" "$code" "$log" "$odir/$name.olean" >> "$results"
      tail -1 "$results"
      exit 0
    fi
  done
  sleep 3
done
