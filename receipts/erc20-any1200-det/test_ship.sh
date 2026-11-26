#!/usr/bin/env bash
set -uo pipefail
source ~/work/leanenv.sh
H=~/work/solar-g/tools/certify/erc20_any; t=~/work/det/shiptest; rm -rf $t; mkdir -p $t/out
cd ~/work/sl
tc=$HOME/.elan/toolchains/leanprover--lean4---v4.35.0
# A check_final.log of the closure that is built here: every olean under the project's build dirs, plus one toolchain module.
{ echo "MODULE Init.Prelude $tc/lib/lean/Init/Prelude.olean trusted"
  find $PWD/.lake/build/lib/lean $PWD/.lake/packages/*/.lake/build/lib/lean $PWD/vendor/*/.lake/build/lib/lean -name '*.olean' 2>/dev/null \
   | sort | awk '{ m=$0; sub(/.*\/lib\/lean\//, "", m); sub(/\.olean$/, "", m); gsub("/", ".", m); print "MODULE " m " " $0 " replay" }'
} > $t/out/check_final.log
cp ~/work/cand/fresh.json $t/out/fresh.json
echo "modules $(grep -c ^MODULE $t/out/check_final.log)"
awk '$1=="MODULE"{print $3}' $t/out/check_final.log | while read p; do echo "replay x $(sha256sum < $p | cut -c1-64) $p"; done > $t/plan
bash $H/pack.sh $PWD $t/out $t/ship; echo "pack exit=$?"
S=$(cat $t/ship/ship.sha256); ls -l $t/ship/ship.tar | awk '{print "tar bytes",$5}'
# Remove every archived olean, then restore from the archive.
awk '$1=="MODULE" && $3 !~ /elan/ {print $3}' $t/out/check_final.log | xargs rm -f
bash $H/unpack.sh $t/ship $S $t/plan $t/u1; echo "unpack exit=$? (want 0)"
bash $H/unpack.sh $t/ship 0000000000000000000000000000000000000000000000000000000000000000 $t/plan $t/u2; echo "unpack wrong-sha exit=$? (want 4)"
sed '2s/ [0-9a-f]\{64\} / 1111111111111111111111111111111111111111111111111111111111111111 /' $t/plan > $t/plan.bad
bash $H/unpack.sh $t/ship $S $t/plan.bad $t/u3; echo "unpack tampered-plan exit=$? (want 4)"; tail -2 $t/u3/precheck
