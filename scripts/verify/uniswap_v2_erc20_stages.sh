#!/usr/bin/env bash
# Export solar's stages of the Uniswap V2 port's UniswapV2ERC20 into Certified/uv2_erc20/gen, before
# the build of the uv2_erc20 library (Contracts/UniswapV2/ERC20/SourceMir.lean imports its Stage0).
# They are not committed: they are compiled from the GPL-3.0 v2-core port, as Source.lean is.
#
#   SOLAR=path/to/solar scripts/verify/uniswap_v2_erc20_stages.sh
#
# Needs scripts/verify/uniswap_v2_gen.sh's port (.cache/uniswap-v2/src). SOLAR is a solar binary
# built from the solar commit under test (default: solar on PATH). Compiles with the slice's options
# (Certified/uv2_erc20/options: -Ogas --evm-version osaka) and -Zemit-lean-stages, checks that the
# flag does not change the runtime bytecode, and fails if Stage0.lean is missing afterwards.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/../.."
SOLAR="${SOLAR:-solar}"
src=.cache/uniswap-v2/src
[[ -s $src/UniswapV2ERC20.sol ]] || { echo "error: $src/UniswapV2ERC20.sol missing; run scripts/verify/uniswap_v2_gen.sh" >&2; exit 1; }
mapfile -t opts < Certified/uv2_erc20/options
out="$(pwd)/Certified/uv2_erc20/gen"
tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
rm -rf "$out"
(cd "$src" && "$SOLAR" "${opts[@]}" --emit bin-runtime UniswapV2ERC20.sol) > "$tmp/plain.json"
(cd "$src" && "$SOLAR" "${opts[@]}" -Zemit-lean-stages="$tmp/stages" --emit bin-runtime UniswapV2ERC20.sol) > "$tmp/staged.json"
cmp -s "$tmp/plain.json" "$tmp/staged.json" \
  || { echo "error: -Zemit-lean-stages changed the runtime bytecode" >&2; exit 1; }
mkdir -p "$out"
cp -r "$tmp/stages/UniswapV2ERC20" "$out/"
[[ -s $out/UniswapV2ERC20/Stage0.lean ]] || { echo "error: no Stage0.lean exported" >&2; exit 1; }
python3 scripts/verify/uniswap_v2_erc20_mutants.py "$out" >/dev/null
echo "wrote $out/UniswapV2ERC20 ($("$SOLAR" --version | sed -n 's/^Commit SHA: //p'))"
