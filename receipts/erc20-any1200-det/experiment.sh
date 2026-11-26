#!/usr/bin/env bash
# Determinism experiment: rebuild single modules repeatedly and hash their oleans.
set -uo pipefail
source ~/work/leanenv.sh
cd ~/work/sl
o=~/work/det/out; mkdir -p $o
log() { echo "$* $(date -u +%FT%TZ)" | tee -a $o/results; }
lib=.lake/build/lib/lean
wipe() { local p=$1; rm -f $lib/$p.olean $lib/$p.ilean $lib/$p.trace $lib/$p.hash $lib/$p.olean.hash $lib/$p.ilean.hash .lake/build/ir/$p.c .lake/build/ir/$p.c.hash .lake/build/ir/$p.setup.json; }
one() { # tag threads module path
  local tag=$1 th=$2 m=$3 p=$4
  wipe $p
  LEAN_NUM_THREADS=$th lake -KleanMemory=6000 build $m > $o/$tag.log 2>&1; local rc=$?
  cp $lib/$p.olean $o/$tag.olean 2>/dev/null
  log "$tag module=$m threads=$th exit=$rc olean=$(sha256sum < $lib/$p.olean | cut -c1-64) ilean=$(sha256sum < $lib/$p.ilean | cut -c1-64)"
}
A=SolidCore.Refinement.Solar.AssembleCallWorld; AP=SolidCore/Refinement/Solar/AssembleCallWorld
lake -KleanMemory=6000 build $A > $o/first.log 2>&1; log "first build of $A exit=$?"
for i in 1 2 3; do one acw-t12-$i 12 $A $AP; done
for i in 1 2; do one acw-t1-$i 1 $A $AP; done
for i in 1 2; do one acw-t5-$i 5 $A $AP; done
# The uv2 Manifest from two independent exports, raw and normalized.
M=uv2_erc20.gen.UniswapV2ERC20.Manifest; MP=uv2_erc20/gen/UniswapV2ERC20/Manifest
g=Certified/uv2_erc20/gen/UniswapV2ERC20
for v in exp1 exp2 n1 n2; do cp ~/work/det/$v/UniswapV2ERC20/Manifest.lean $g/Manifest.lean; one man-$v 12 $M $MP; done
log "DONE"
