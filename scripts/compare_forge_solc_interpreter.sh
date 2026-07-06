#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SOLC_BIN="${SOLC:-/Users/dan/.solc-select/artifacts/solc-0.8.35/solc-0.8.35}"
LAKE_BIN="${LAKE:-/Users/dan/.elan/bin/lake}"
FORGE_BIN="${FORGE:-forge}"

usage() {
  cat <<USAGE
Usage: $(basename "$0") [harness args]

Runs paired cases from tests/forge-harness/manifest.json:
  1. Forge tests compiled by regular solc
  2. Matching Lean Solidity-interpreter witnesses

Environment:
  SOLC      Real solc executable. Default: pinned solc 0.8.35 artifact
  LAKE      Lake executable. Default: /Users/dan/.elan/bin/lake
  FORGE     Forge executable. Default: forge
  KEEP_TMP  Set to 1 to keep logs/artifacts under the temp directory.

Examples:
  $(basename "$0")
  $(basename "$0") --only checked-arithmetic
USAGE
}

if [[ "${1:-}" == "-h" || "${1:-}" == "--help" ]]; then
  usage
  exit 0
fi

python3 "$ROOT/scripts/run_forge_interpreter_harness.py" \
  --solc "$SOLC_BIN" \
  --lake "$LAKE_BIN" \
  --forge "$FORGE_BIN" \
  "$@"
