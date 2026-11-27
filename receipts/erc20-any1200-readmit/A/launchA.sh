#!/usr/bin/env bash
# Slot A (READMIT): build, pack (SHIP_OUT), replay what it can, then negatives. DEADLINE is $1.
export CANDIDATE_SHA256=166137ef66c1d792afd5b39bf5e3a1b02402f6c4484032f8b4115d926dd1245a
unit=$(cat /proc/self/cgroup | sed 's/^0:://')
mkdir -p ~/w/cgraw
( while :; do for c in /sys/fs/cgroup/erc20cap-*; do [[ -d $c ]] || continue; n=$(basename $c); cat $c/memory.peak > ~/w/cgraw/$n.memory.peak 2>/dev/null; cat $c/memory.events > ~/w/cgraw/$n.memory.events 2>/dev/null; done; sleep 2; done ) & cgs=$!
snap_unit() { cat /sys/fs/cgroup$unit/memory.peak > ~/w/cgraw/unit.memory.peak; cat /sys/fs/cgroup$unit/memory.events > ~/w/cgraw/unit.memory.events; echo "$unit" > ~/w/cgraw/unit.path; }
d=$1; L=~/launchA.txt
echo "launch $(date -u +%FT%TZ) slot=A CANDIDATE_SHA256=$CANDIDATE_SHA256 deadline=$d" > $L
bash ~/box_setup.sh >> $L 2>&1 || { echo "setup failed" >> $L; exit 1; }
source ~/w/env.sh; cd ~/w/solidity-lean
# Raw (unnormalized) export from the pinned binary, archived beside the run's normalized one.
export SOLC=$HOME/.cache/solc/solc-0.8.35
bash scripts/verify/uniswap_v2_gen.sh > ~/w/raw-export.log 2>&1 && SOLAR=~/w/candidate-bin/solar bash scripts/verify/uniswap_v2_erc20_stages.sh >> ~/w/raw-export.log 2>&1; echo "raw export exit=$? $(date -u +%FT%TZ)" >> $L
rm -rf ~/w/raw-export && cp -r Certified/uv2_erc20/gen ~/w/raw-export
SHIP_OUT=$HOME/w/ship bash ~/w/solar/tools/certify/erc20_any/slot.sh A "$d" >> $L 2>&1
echo "slot.sh exit=$? $(date -u +%FT%TZ)" >> $L
rm -rf ~/w/norm-export && cp -r ~/w/solidity-lean/Certified/uv2_erc20/gen ~/w/norm-export
bash ~/w/solar/tools/certify/erc20_any/neg.sh ~/w/solidity-lean ~/w/slotA/out > ~/w/slotA/neg.log 2>&1
echo "neg.sh exit=$? $(date -u +%FT%TZ)" >> $L
snap_unit; kill $cgs
echo "launch done $(date -u +%FT%TZ)" >> $L
