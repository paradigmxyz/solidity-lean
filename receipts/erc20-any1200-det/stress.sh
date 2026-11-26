#!/usr/bin/env bash
set -uo pipefail
source ~/work/leanenv.sh; cd ~/work/sl
o=~/work/det/out; lib=.lake/build/lib/lean; p=SolidCore/Refinement/Solar/AssembleCallWorld
for k in 1 2 3 4 5 6; do ( while :; do :; done ) & done; pids=$(jobs -p)
for i in $(seq 1 10); do
  rm -f $lib/$p.olean $lib/$p.ilean $lib/$p.trace $lib/$p.hash $lib/$p.olean.hash $lib/$p.ilean.hash
  LEAN_NUM_THREADS=48 lake -KleanMemory=6000 build SolidCore.Refinement.Solar.AssembleCallWorld > $o/stress-$i.log 2>&1
  echo "stress-$i threads=48 cpu-saturated exit=$? olean=$(sha256sum < $lib/$p.olean | cut -c1-64) $(date -u +%FT%TZ)" | tee -a $o/results
  cp $lib/$p.olean $o/stress-$i.olean
done
kill $pids
echo STRESSDONE | tee -a $o/results
