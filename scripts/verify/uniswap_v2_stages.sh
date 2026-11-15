#!/usr/bin/env bash
# Generate UniswapV2ERC20.transfer's slice before the build of the uv2_erc20 library: the exported
# stages, the backend stages' proofs, the bytes certificates and the gas certificate. None is
# committed: each is compiled from the GPL-3.0 v2-core port.
#
#   scripts/verify/uniswap_v2_gen.sh      # first: the port under .cache/uniswap-v2/src
#   scripts/verify/uniswap_v2_stages.sh
#   lake build -KleanMemory=6000 uv2_erc20 ContractsUniswapV2ERC20SourceMir
#
# Needs a solar checkout at the commit in scripts/verify/uniswap_v2_stages-solar-rev (SOLAR_DIR,
# default .cache/solar-stages) and its solar binary (SOLAR, default
# $SOLAR_DIR/target/release/solar, built here when missing). Writes, under Certified/uv2_erc20/:
#   gen/UniswapV2ERC20/  solar -Zemit-lean-stages of the port (scripts/verify/uniswap_v2_erc20_stages.sh,
#                        with its stage0 mutants in gen/UniswapV2ERC20Mut);
#   CtxGas.lean          the checker with contexts and gas on the exact bytes against the final EVM
#                        IR, transfer's slice only (scripts/verify/uniswap_v2_gas.sh);
#   ProofsT/             tools/certify/certify.py: each stage's refinement for the calls of
#                        transfer(address,uint256) (every other selector excluded), cut block by
#                        block so each module stays within 6 GB, and their composition
#                        (ProofsT/Stages.lean);
#   Ctx.lean             tools/certify/asm_ctx.py: the checker with contexts and STATICCALL
#                        (checkXB) accepts the exact runtime bytecode against the final EVM IR. Its
#                        bytes theorem is stated only for call-free bytes (AssembleNoCall); this
#                        contract's bytes make calls (permit's ecrecover STATICCALL), so Ctx states
#                        not_call_free and no bytes theorem (the gas certificate's guard route
#                        gives the bytes for transfer's calls);
#   CtxNeg.lean          the checker refuses the bytes with one byte changed (negative controls).
# Fails if any step fails or any module is missing afterwards.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/../.."

rev="$(tr -d '[:space:]' < scripts/verify/uniswap_v2_stages-solar-rev)"
SOLAR_DIR="${SOLAR_DIR:-.cache/solar-stages}"
if ! git -C "$SOLAR_DIR" rev-parse --git-dir >/dev/null 2>&1; then
  git init -q "$SOLAR_DIR"
  git -C "$SOLAR_DIR" remote add origin https://github.com/paradigmxyz/solar.git
fi
if [[ "$(git -C "$SOLAR_DIR" rev-parse -q --verify HEAD 2>/dev/null || true)" != "$rev" ]]; then
  git -C "$SOLAR_DIR" fetch -q --depth 1 origin "$rev"
  git -C "$SOLAR_DIR" checkout -q --detach "$rev"
fi
SOLAR_DIR="$(realpath "$SOLAR_DIR")"
SOLAR="${SOLAR:-$SOLAR_DIR/target/release/solar}"
if [[ ! -x "$SOLAR" || "$(cat "$SOLAR_DIR/target/.stages-rev" 2>/dev/null)" != "$rev" ]]; then
  cargo build --release --locked --manifest-path "$SOLAR_DIR/Cargo.toml" --bin solar
  echo "$rev" > "$SOLAR_DIR/target/.stages-rev"
fi
SOLAR="$(realpath "$SOLAR")"
for f in tools/certify/certify.py tools/certify/asm_ctx.py tools/certify/gen_ctxgas.py; do
  [[ -s "$SOLAR_DIR/$f" ]] || { echo "error: solar $rev has no $f" >&2; exit 1; }
done

out=Certified/uv2_erc20
gen="$out/gen/UniswapV2ERC20"
# The stages and the gas certificate (the gas script exports the stages first).
SOLAR_DIR="$SOLAR_DIR" SOLAR="$SOLAR" scripts/verify/uniswap_v2_gas.sh

# The scope: calls of transfer(address,uint256); every other external function is excluded.
excluded=(
  '06fdde03=name()'
  '95d89b41=symbol()'
  '313ce567=decimals()'
  '18160ddd=totalSupply()'
  '70a08231=balanceOf(address)'
  'dd62ed3e=allowance(address,address)'
  '3644e515=DOMAIN_SEPARATOR()'
  '30adf81f=PERMIT_TYPEHASH()'
  '7ecebe00=nonces(address)'
  'd505accf=permit(address,address,uint256,uint256,uint8,bytes32,bytes32)'
  '095ea7b3=approve(address,uint256)'
  '23b872dd=transferFrom(address,address,uint256)'
)
args=()
for e in "${excluded[@]}"; do args+=(--exclude "$e"); done
rm -rf "$out/ProofsT" "$out/ProofsT.lean" "$out/Ctx.lean" "$out/CtxNeg.lean"
python3 "$SOLAR_DIR/tools/certify/certify.py" "$gen" --gen-module uv2_erc20.gen.UniswapV2ERC20 \
  --proof-dir "$out/ProofsT" --proof-module uv2_erc20.ProofsT \
  --namespace SolarTV.Milestone.Uv2Erc20T --label uv2_erc20_transfer \
  --cut --joins --no-mir-joins --segment 8 "${args[@]}"
python3 "$SOLAR_DIR/tools/certify/asm_ctx.py" "$gen" --gen-module uv2_erc20.gen.UniswapV2ERC20 \
  --out "$out/Ctx.lean" --neg-out "$out/CtxNeg.lean" --module uv2_erc20.Ctx

# The last EVM IR stage is the one before assemble; how many passes change the code depends on
# the compiler, so it is read from the manifest.
last=$(python3 -c 'import json,sys; s=[x for x in json.load(open(sys.argv[1]))["stages"] if x["pass"]!="assemble"]; print(s[-1]["file"])' "$gen/manifest.json")
status=0
for f in "$gen/Stage0.lean" "$gen/Sched.lean" "$gen/$last" "$gen/Bytecode.lean" "$out/CtxGas.lean" \
    "$out/ProofsT/Stages.lean" "$out/ProofsT/Assembly.lean" "$out/Ctx.lean" "$out/CtxNeg.lean"; do
  [[ -s $f ]] || { echo "error: $f was not generated" >&2; status=1; }
done
exit "$status"
