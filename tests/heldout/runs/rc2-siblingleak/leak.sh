#!/usr/bin/env bash
# SiblingLeak certify on driver 0479b90a / base 49d1d7f5, the pins of rc2-acc5-siblingok (its matching positive).
source ~/.elan/env
export LEAN_MEMORY=6000 LEAN_NUM_THREADS=1
R=$HOME/w/rc2; rm -rf $R/leak-work $R/leak-rec
cd ~/w/drv047
python3 ~/w/t5/scripts/verify/mutant/generic/receipt.py --out $R/leak-receipt.json --   tools/certify/certify $R/src/SiblingLeak.sol natspec --solidity-lean ~/w/sl --base 49d1d7f5d9b74165486bd9f634202bee1a3633eb   --work $R/leak-work --record-dir $R/leak-rec --packages-from ~/w/sl --probe-cache ~/w/mut
echo "LEAK-DONE exit=$?"
