#!/usr/bin/env bash
# Before/after for the six generated EVM run proofs: original module vs Skip copy.
set -uo pipefail
source ~/env.sh; cd ~/bench/sl; OUT=~/bench/sk; mkdir -p $OUT
for rep in 1 2; do for m in Evm1 Evm2 Evm3 Evm4 Evm5 Sched; do for mode in orig sk; do
  if [ $mode = orig ]; then f=Certified/flag_4ce5cf9a/Proofs/Runs/$m.lean; else f=Certified/Skip/Runs/$m.lean; fi
  t=$OUT/$m.$mode.$rep
  ~/bench/slot.sh ~/bench/harness/memtime.py $t.time lake env lean -M 6000 -DmaxHeartbeats=1000000 -Dbackward.do.legacy=true -Dprofiler=true -o $t.olean $f > $t.out 2>&1
  echo "$m $mode $rep exit $? $(grep Elapsed $t.time | awk '{print $8}')"
done; done; done
for m in Evm1 Evm2 Evm3 Evm4 Evm5 Sched; do
  ~/bench/slot.sh ~/bench/harness/memtime.py $OUT/$m.orig.kernel.time lake env lean --run ~/bench/harness/Kernel.lean flag_4ce5cf9a.Proofs.Runs.$m $OUT/$m.orig.kernel.csv 2>&1 | tail -1
  ~/bench/slot.sh ~/bench/harness/memtime.py $OUT/$m.sk.kernel.time lake env lean --run ~/bench/harness/Kernel.lean Skip.Runs.$m $OUT/$m.sk.kernel.csv 2>&1 | tail -1
done
~/bench/slot.sh lake env lean --run ~/bench/harness/CompareSK.lean > $OUT/compare.csv 2>&1; cat $OUT/compare.csv
sha256sum .lake/build/lib/lean/flag_4ce5cf9a/Proofs/Runs/*.olean .lake/build/lib/lean/flag_4ce5cf9a/{Lowering,SpecConnect}.olean | cut -c1-16,66- > $OUT/olean_sha.txt
for m in Evm1 Evm2 Evm3 Evm4 Evm5 Sched; do a=$(sha256sum < .lake/build/lib/lean/flag_4ce5cf9a/Proofs/Runs/$m.olean); b=$(sha256sum < $OUT/$m.orig.1.olean); c=$(sha256sum < $OUT/$m.orig.2.olean); echo "$m lake-vs-direct $([ "$a" = "$b" ] && [ "$b" = "$c" ] && echo identical || echo differs)"; done >> $OUT/olean_sha.txt
touch $OUT/done
