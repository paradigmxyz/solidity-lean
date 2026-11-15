#!/usr/bin/env bash
# Lane G: the remaining measurement runs, strictly one admission slot at a time.
cd "$(git rev-parse --show-toplevel)"
for f in Real/AbiHash Real/Masks Real/Events Tests Cbv/Sat; do
  scripts/eval/check.sh G Verify/Eval/G/$f.lean > ~/g-gen/check-$(echo $f | tr / _).out 2>&1
done
LEAN_PATH=~/g-build scripts/eval/check.sh G Verify/Eval/G/Cbv/Mulx.lean > ~/g-gen/check-Cbv_Mulx.out 2>&1
G_NEGATE='^Vault\.withdraw#0$' G_ONLY='^Vault\.withdraw#0$' G_BACKENDS='vc_valid vc_grind' G_LIMIT=60 Verify/Eval/G/discharge_g.sh Vault ~/g-gen/discharge-neg/Vault > ~/g-gen/neg-vault.log 2>&1
G_NEGATE='^ArrayMax\.max#8$' G_ONLY='^ArrayMax\.max#8$' G_BACKENDS='vc_valid vc_grind' G_LIMIT=60 Verify/Eval/G/discharge_g.sh ArrayMax ~/g-gen/discharge-neg/ArrayMax > ~/g-gen/neg-arraymax.log 2>&1
G_ONLY='^ArrayMax\.max#([3-9]|1[0-9])$|clamp|ArrayMaxEntry' G_BACKENDS='vc_valid vc_grind cert' G_LIMIT=60 Verify/Eval/G/discharge_g.sh ArrayMax ~/g-gen/discharge/ArrayMax-b > ~/g-gen/arraymax-b.log 2>&1
echo CHAIN-DONE
