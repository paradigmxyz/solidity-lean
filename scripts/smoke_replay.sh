#!/usr/bin/env bash
# Fast development smoke replay: a curated subset of the differential corpus,
# Lean-side only (Forge skipped). Use this in the edit/build/check loop while
# developing the interpreter; run the full replay
# (scripts/compare_forge_solc_interpreter.sh) at phase boundaries before commit.
#
# Why this is fast and still meaningful:
#   * Only the Lean interpreter changes during development; the Forge fixtures and
#     tests never do. `--skip-forge` drops the per-case solc-compile + Foundry-EVM
#     run (the dominant cost) while STILL generating each witness from the solc AST
#     and validating that the Lean `#eval`s return `true`. A Lean regression (wrong
#     value or a build/elaboration error) is caught exactly as in the full replay.
#   * The case set is curated for coverage, not exhaustiveness: every case that
#     exercises the external-call / creation / interaction paths (the Phase 5
#     surface), plus broad evaluator/statement/ABI/reference sentinels. The
#     minute-plus heavy contracts (erc721-royalty, erc1155-supply variants,
#     checkpoints, uniswap-v3-math, frontend-frontier) are intentionally excluded;
#     they run in the full replay.
#
# Usage:
#   scripts/smoke_replay.sh                 # curated subset, Lean only
#   SMOKE_WITH_FORGE=1 scripts/smoke_replay.sh   # also run Forge for the subset
#   scripts/smoke_replay.sh --only foo --only bar  # extra explicit cases appended
#
# Environment (same defaults as compare_forge_solc_interpreter.sh):
#   SOLC   pinned solc 0.8.35 artifact
#   LAKE   lake executable
#   FORGE  forge executable (only used when SMOKE_WITH_FORGE=1)

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SOLC_BIN="${SOLC:-/Users/dan/.solc-select/artifacts/solc-0.8.35/solc-0.8.35}"
LAKE_BIN="${LAKE:-/Users/dan/.elan/bin/lake}"
FORGE_BIN="${FORGE:-forge}"

# --- curated smoke set -------------------------------------------------------
# Phase 5 external-effect surface (calls / creates / interaction transcripts):
EXTERNAL_CASES=(
  try-catch
  contract-creation
  create-options
  high-level-call-options
  low-level-call-options
  uniswap-transfer-helper
  dapphub-weth9
  openzeppelin-vesting-wallet
  openzeppelin-payment-splitter
  openzeppelin-refund-escrow
  openzeppelin-multicall
  compound-timelock
  abi-malformed
  abi-function-values
  base-constructor-runtime-args
)
# Broad evaluator / statement / storage / reference / ABI / event sentinels:
SENTINEL_CASES=(
  checked-arithmetic
  storage-counter
  mapping-index
  loop-control
  tuple-destructure
  expression-control
  reference-assignments
  reference-mapping-storage
  event-emitter
  custom-error
  abi-struct-tuples
  openzeppelin-erc20
  modifier-order
)

ONLY_ARGS=()
for c in "${EXTERNAL_CASES[@]}" "${SENTINEL_CASES[@]}"; do
  ONLY_ARGS+=(--only "$c")
done

FORGE_ARGS=(--skip-forge)
if [[ "${SMOKE_WITH_FORGE:-0}" == "1" ]]; then
  FORGE_ARGS=()
fi

# Run cases concurrently (the machine has many cores; each case is an independent
# solc + lean subprocess). Override with SMOKE_JOBS.
JOBS="${SMOKE_JOBS:-10}"

echo "smoke_replay: $(( ${#EXTERNAL_CASES[@]} + ${#SENTINEL_CASES[@]} )) curated cases, jobs=$JOBS, forge=$([[ ${#FORGE_ARGS[@]} -eq 0 ]] && echo on || echo skipped)"

python3 "$ROOT/scripts/run_forge_interpreter_harness.py" \
  --solc "$SOLC_BIN" \
  --lake "$LAKE_BIN" \
  --forge "$FORGE_BIN" \
  --timeout 900 \
  --jobs "$JOBS" \
  "${FORGE_ARGS[@]}" \
  "${ONLY_ARGS[@]}" \
  "$@"
