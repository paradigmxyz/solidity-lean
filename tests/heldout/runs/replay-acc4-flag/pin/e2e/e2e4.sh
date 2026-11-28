#!/usr/bin/env bash
# One end-to-end pin case (stale-bytes@pin) against acc4-flag through the unmodified driver at 6d0f2621.
source ~/.elan/env
export SOLAR_VERIFY_Z3=$HOME/z3env/bin/z3 LEAN_MEMORY=6000 LEAN_NUM_THREADS=1
W=$HOME/w/acc4/pin-e2e
rm -rf $W; mkdir -p $W
cd ~/w/drv6d
python3 ~/w/t5/scripts/verify/mutant/generic/negatives.py --replay-from ~/w/acc4/rec/Certified/record/acc4-flag/replay \
  --replay 'tools/certify/certify --replay {dir} --solidity-lean ~/w/sl --work {work} --packages-from ~/w/sl --probe-cache ~/w/mut' \
  --slot "python3 ~/w/t5/scripts/verify/mutant/generic/receipt.py --out $W/receipt.json --" \
  --layer pin --only stale-bytes@pin --heldout ~/w/t5/tests/heldout --solar ~/w/bin697/solar --work $W --table $W/table.md
echo "E2E-DONE exit=$?"
