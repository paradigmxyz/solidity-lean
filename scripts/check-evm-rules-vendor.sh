#!/usr/bin/env bash
# Compare the vendored EvmRules library with a solar checkout's scripts/evm-rules/lean.
# Usage: scripts/check-evm-rules-vendor.sh SOLAR_DIR
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
solar="${1:?usage: check-evm-rules-vendor.sh SOLAR_DIR}"
diff -r "$solar/scripts/evm-rules/lean/EvmRules.lean" "$root/vendor/evm-rules/EvmRules.lean"
diff -r "$solar/scripts/evm-rules/lean/EvmRules" "$root/vendor/evm-rules/EvmRules"
echo "vendor/evm-rules matches $solar"
