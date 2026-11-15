#!/usr/bin/env bash
# Run Lane A's baseline over the SolM fixtures, breadth-first (every family at 16, then 32, ...).
#
#   scripts/eval/fixtures/run_baseline.sh [families] [sizes]
#   (defaults: "Straight Shared Branch Memory LoopBody" and "16 32 64 128 256")
#
# Each fixture goes through scripts/eval/check.sh (one at a time), writing its .olean next to the
# repository's build so Verify/Eval/A/Replay.lean can import it; then the kernel-only replay runs
# on it (~/eval-logs/replay-A-<Fixture>.jsonl). A family stops at the first size that fails, runs
# out of memory (check.sh's -M cap, 5000 MB) or whose Lean process runs longer than EVAL_TIMEOUT
# seconds (default 600; the clock starts when Lean starts, not while check.sh waits for a slot).
# That outcome is recorded as a receipt row with "status" set, and the family's larger sizes are
# skipped.
set -u
repo="$(cd "$(dirname "$0")/../../.." && pwd)"
cd "$repo"
[ -f "$HOME/env.sh" ] && source "$HOME/env.sh"
fams="${1:-Straight Shared Branch Memory LoopBody}"
sizes="${2:-16 32 64 128 256}"
limit="${EVAL_TIMEOUT:-600}"
receipts="${EVAL_RECEIPTS:-$HOME/eval-receipts.jsonl}"
odir="$repo/.lake/build/lib/lean/Verify/Eval/A/Fixtures"
mkdir -p "$odir" "$HOME/eval-logs"
declare -A stopped
for n in $sizes; do
  for fam in $fams; do
    [ -n "${stopped[$fam]:-}" ] && continue
    name="$fam$n"; f="Verify/Eval/A/Fixtures/$name.lean"
    rm -f "$odir/$name.olean"
    scripts/eval/check.sh A "$f" -o "$odir/$name.olean" > "$HOME/eval-logs/run-A-$name.out" 2>&1 &
    cpid=$!
    lt0=""; timed_out=""
    while kill -0 "$cpid" 2>/dev/null; do
      lpid=$(pgrep -f "^(\S*/)?lean .*Fixtures/$name\.lean" | head -1)
      if [ -n "$lpid" ]; then
        [ -z "$lt0" ] && lt0=$(date +%s)
        if [ $(( $(date +%s) - lt0 )) -gt "$limit" ]; then
          timed_out=1; kill "$lpid" 2>/dev/null; sleep 10; kill -9 "$lpid" 2>/dev/null
        fi
      fi
      sleep 3
    done
    wait "$cpid"; code=$?
    lean_s=$(( $(date +%s) - ${lt0:-$(date +%s)} ))
    status=ok
    log=$(ls -t "$HOME"/eval-logs/*-A-"$name".log 2>/dev/null | head -1)
    if [ -n "$timed_out" ]; then status=timeout
    elif [ -n "$log" ] && grep -qiE 'out of memory|memory (limit|threshold)|maximum memory|memory exhausted|excessive memory' "$log"; then status=oom
    elif [ $code -ne 0 ]; then status=error; fi
    if [ "$status" != ok ]; then
      printf '{"lane":"A","file":"%s","exit":%d,"status":"%s","wall_s":%d,"limit_s":%s,"log":"%s"}\n' \
        "$f" "$code" "$status" "$lean_s" "$limit" "$log" >> "$receipts"
      stopped[$fam]=$status
      echo "[run] $name: $status after $lean_s s of Lean; stopping $fam"
      continue
    fi
    echo "[run] $name: ok in $lean_s s"
    if [ -f "$odir/$name.olean" ]; then
      lake env lean --run Verify/Eval/A/Replay.lean "Verify.Eval.A.Fixtures.$name" > "$HOME/eval-logs/replay-A-$name.jsonl" 2>&1
      echo "[run] $name: replay exit $?"
    fi
  done
done
