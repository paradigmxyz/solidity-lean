#!/usr/bin/env bash
# Mutation acceptance for UniswapV2ERC20.transfer's certified statement
# (docs/MUTATIONS_TRANSFER.md): one build of ContractsUniswapV2ERC20Certified, then each mutation
# of mutate.py recompiled in an overlay (the tree is never edited) and a table of
# mutation -> rejected by. Exits 0 iff every mutation is rejected and both controls pass.
#
#   SOLAR_DIR=<solar checkout> scripts/verify/mutant/transfer/run.sh [--skip-gen] [--only a,b]
#
# SOLAR_DIR: the solar checkout scripts/verify/uniswap_v2_stages-solar-rev names, with its release
# solar built (its tools/certify/gen_ctxgas.py regenerates the bytes mutants' certificates).
# SOLAR_VERIFY: solar-verify for uniswap_v2_transfer_slice.sh. --skip-gen keeps the generated
# modules already in the tree (uniswap_v2_gen.sh, uniswap_v2_stages.sh, uniswap_v2_transfer_slice.sh).
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
here=scripts/verify/mutant/transfer
gen=1
args=()
while [[ $# -gt 0 ]]; do
  case "$1" in
    --skip-gen) gen=0 ;;
    --only) args+=(--only "$2"); shift ;;
    *) echo "usage: $0 [--skip-gen] [--only a,b]" >&2; exit 2 ;;
  esac
  shift
done
export LEAN_NUM_THREADS=1
if [[ $gen == 1 ]]; then
  scripts/verify/uniswap_v2_gen.sh
  scripts/verify/uniswap_v2_stages.sh
  # The slice's generator probes the checked contract, so Core is built first.
  lake -R -KleanMemory=6000 build Contracts.UniswapV2.ERC20.Core
  scripts/verify/uniswap_v2_transfer_slice.sh
fi
lake -R -KleanMemory=6000 build ContractsUniswapV2ERC20Certified
mkdir -p .lake/mutant-transfer
python3 "$here/mutate.py" --table .lake/mutant-transfer/table.md "${args[@]}"
