#!/usr/bin/env bash
# Per-module measurement of the generated acc4-flag modules (see docs/eval/acc4.md).
# For each module in import order: lake builds its olean (so later modules import it), then a
# separate measured run re-elaborates it with the trace profiler, under /usr/bin/time, and the
# kernel recheck harness re-adds each declaration to the kernel alone.
set -uo pipefail
source ~/env.sh
SL=~/bench/sl; OUT=~/bench/out; H=~/bench/harness
mkdir -p $OUT/trace $OUT/time $OUT/kernel
cd $SL
OPTS="-DmaxHeartbeats=1000000 -Dbackward.do.legacy=true -Dtrace.profiler=true -Dtrace.profiler.threshold=1"
for m in "$@"; do
  f=Certified/$(echo $m | tr . /).lean
  echo "== $m $(date -u +%FT%TZ)"
  ~/bench/slot.sh lake -R build -KleanMemory=9000 $m 2>&1 | grep -E 'error|warning: .*sorry|Build completed' | tail -3
  ~/bench/slot.sh ~/bench/harness/memtime.py $OUT/time/$m.txt lake env lean --json $OPTS $f > $OUT/trace/$m.jsonl 2> $OUT/trace/$m.err
  echo "elab exit $? rss_kb $(grep 'Maximum resident' $OUT/time/$m.txt | awk '{print $6}') wall $(grep 'Elapsed' $OUT/time/$m.txt | awk '{print $8}')"
  ~/bench/slot.sh ~/bench/harness/memtime.py $OUT/time/$m.kernel.txt lake env lean --run $H/Kernel.lean $m $OUT/kernel/$m.csv 2>&1 | tail -1
done
