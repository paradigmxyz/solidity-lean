#!/usr/bin/env bash
# A/B: elaborate a generated module with the kernel_rfl clone code interpreted (as today) or
# native (its two modules' dynlibs loaded). Same oleans, file and options; writes each run's olean.
set -uo pipefail
source ~/env.sh; cd ~/bench/sl; OUT=~/bench/ab; mkdir -p $OUT
D=.lake/build/lib/lean
NATIVE="--load-dynlib=$D/solidity_x2dlean_SolidCore_Refinement_Kernel.so --load-dynlib=$D/solidity_x2dlean_SolidCore_Refinement_KernelRfl.so"
REPS=${REPS:-3}
for rep in $(seq 1 $REPS); do for m in "$@"; do for mode in interp native; do
  f=Certified/$(echo $m | tr . /).lean; tag=$m.$mode.$rep
  extra=""; [ $mode = native ] && extra="$NATIVE"
  ~/bench/slot.sh ~/bench/harness/memtime.py $OUT/$tag.time lake env lean $extra -DmaxHeartbeats=1000000 -Dbackward.do.legacy=true -Dprofiler=true -o $OUT/$tag.olean $f > $OUT/$tag.out 2>&1
  echo "$tag exit $? $(grep Elapsed $OUT/$tag.time | awk '{print $8}') rss_kb $(grep 'Peak single' $OUT/$tag.time | awk '{print $NF}') tc $(grep -P '\ttype checking' $OUT/$tag.out | awk '{print $3}') interp $(grep -P '\tinterpretation' $OUT/$tag.out | awk '{print $2}')"
done; done; done
