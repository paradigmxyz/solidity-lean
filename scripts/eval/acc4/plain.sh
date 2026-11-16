#!/usr/bin/env bash
# Unprofiled pass: wall time and peak RSS of each generated module, elaborated exactly as the
# build does (package options), no trace. Run after run.sh, which builds the oleans.
set -uo pipefail
source ~/env.sh
cd ~/bench/sl; OUT=~/bench/out; mkdir -p $OUT/plain
for m in "$@"; do
  f=Certified/$(echo $m | tr . /).lean
  ~/bench/slot.sh ~/bench/harness/memtime.py $OUT/plain/$m.txt lake env lean -DmaxHeartbeats=1000000 -Dbackward.do.legacy=true -Dprofiler=true $f > $OUT/plain/$m.out 2>&1
  echo "$m exit $? $(grep Elapsed $OUT/plain/$m.txt | awk '{print $8}') $(grep 'Peak single' $OUT/plain/$m.txt | awk '{print $NF}')"
done
