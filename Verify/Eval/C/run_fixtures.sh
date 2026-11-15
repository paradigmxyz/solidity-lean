#!/usr/bin/env bash
# Run lane C's scaling fixtures through scripts/eval/check.sh, one at a time, and summarize.
#   Verify/Eval/C/run_fixtures.sh [kinds...]      (default: Straight Shared Branch)
# Each Sym run also prints the stepper's counters (-Dverify.eval.c.stats=true). Branch fixtures run
# the stepper three ways: threaded grind goal (default), fresh goal per child, eager refutation.
set -uo pipefail
cd "$(dirname "$0")/../../.."
kinds=("$@"); [ $# -eq 0 ] && kinds=(Straight Shared Branch)
sizes=(16 32 64 128 256); [ -n "${SIZES:-}" ] && read -ra sizes <<< "$SIZES"
out="$HOME/eval-c-runs.tsv"
for k in "${kinds[@]}"; do
  for n in "${sizes[@]}"; do
    for v in Base Sym; do
      f="Verify/Eval/C/Fix/$k$n$v.lean"
      variants=("default")
      [ "$v" = Sym ] && [ "$k" = Branch ] && variants=("default" "fresh" "eager")
      for var in "${variants[@]}"; do
        extra=(-Dverify.eval.c.stats=true)
        [ "$var" = fresh ] && extra+=(-Dverify.eval.c.fresh=true)
        [ "$var" = eager ] && extra+=(-Dverify.eval.c.eager=true)
        [ "$v" = Base ] && extra=(-DmaxHeartbeats=0)
        o="/tmp/evalc-$k$n$v-$var.olean"
        rm -f "$o"
        line=$(timeout 1800 scripts/eval/check.sh C "$f" -o "$o" "${extra[@]}" 2>&1 | tail -1)
        sz=$(stat -c %s "$o" 2>/dev/null || echo 0)
        printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$k" "$n" "$v" "$var" "$sz" "$line" >> "$out"
        echo "$k$n $v $var olean=$sz $line"
      done
    done
  done
done
