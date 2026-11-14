#!/usr/bin/env bash
# Generate UniswapV2ERC20's exported stages and the transfer slice's gas certificate before the
# build of the uv2_erc20 library (Certified/uv2_erc20/Gas.lean). Nothing generated is committed:
# it is derived from the GPL-3.0 v2-core port.
#
#   SOLAR_DIR=... SOLAR=... scripts/verify/uniswap_v2_gas.sh
#
# Needs scripts/verify/uniswap_v2_gen.sh's scripts/verify/uniswap-v2/UniswapV2ERC20.sol, and:
#   SOLAR_DIR  a solar checkout with tools/certify/{asm_cert,asm_ctx,gen_ctxgas}.py;
#   SOLAR      its solar binary (default $SOLAR_DIR/target/release/solar).
# Writes, under Certified/uv2_erc20/ (ignored by git):
#   uv2_erc20.sol             the flattened port the binary compiles;
#   gen/                      solar -Ogas --evm-version osaka -Zemit-lean-stages of it;
#   CtxGas.lean               gen_ctxgas.py's certificate: the checker with contexts and gas on
#                             the exact bytes against the final EVM IR, every block outside
#                             transfer's slice (the dispatcher's jump on 0xa9059cbb) unchecked.
# Fails if any step fails, if the export changes the bytecode, or if the final stage is not evm11.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/../.."
: "${SOLAR_DIR:?set SOLAR_DIR to a solar checkout}"
SOLAR_DIR="$(realpath "$SOLAR_DIR")"
SOLAR="$(realpath "${SOLAR:-$SOLAR_DIR/target/release/solar}")"
src=scripts/verify/uniswap-v2/UniswapV2ERC20.sol
[[ -s $src ]] || { echo "error: $src missing; run scripts/verify/uniswap_v2_gen.sh" >&2; exit 1; }
out=Certified/uv2_erc20
mkdir -p "$out"
outabs="$(realpath "$out")"
cp "$src" "$out/uv2_erc20.sol"
rm -rf "$out/gen"
tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
cp "$out/uv2_erc20.sol" "$tmp/UniswapV2ERC20.sol"
bin() { python3 -c 'import json,sys; d=json.load(sys.stdin)["contracts"]; print([v["bin-runtime"] for k,v in d.items() if k.endswith(":UniswapV2ERC20")][0])'; }
plain=$(cd "$tmp" && "$SOLAR" UniswapV2ERC20.sol -Ogas --evm-version osaka --emit=bin-runtime | bin)
exported=$(cd "$tmp" && "$SOLAR" UniswapV2ERC20.sol -Ogas --evm-version osaka --emit=bin-runtime \
  "-Zemit-lean-stages=$outabs/gen" | bin)
[[ "$plain" == "$exported" ]] || { echo "error: -Zemit-lean-stages changed the bytecode" >&2; exit 1; }
gen="$out/gen/UniswapV2ERC20"
final=$(python3 -c 'import json,sys; s=json.load(open(sys.argv[1]))["stages"]; print([x["definition"] for x in s if x["kind"]=="evm"][-1])' "$gen/manifest.json")
[[ "$final" == evm11 ]] || { echo "error: the final EVM IR is $final, the proofs name evm11" >&2; exit 1; }
python3 "$SOLAR_DIR/tools/certify/gen_ctxgas.py" "$gen" --module-prefix uv2_erc20.gen.UniswapV2ERC20 \
  --contract UniswapV2ERC20 --final "$final" --selector 0xa9059cbb --out "$out/CtxGas.lean"
echo "wrote $out/gen $out/CtxGas.lean ($(( ${#plain} / 2 )) bytes)"
