#!/bin/bash
# Negative controls for verify_binding.sh: one per pin (exit 2, naming the pin), and artifact
# mismatches with every pin intact (exit 1). Prints one line per control; exits 0 iff every control
# exits as required.
set -uo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
here="$root/Certified/uv2_transfer_e6"
: "${SOLAR_DIR:?set SOLAR_DIR}"
t=$(mktemp -d); trap 'rm -rf "$t"' EXIT
src=$root/scripts/verify/uniswap-v2/UniswapV2ERC20.sol
solar=$root/.cache/solar-stages/target/release/solar
sv=$SOLAR_DIR/target/release/solar-verify
ok=0
run() {  # name, required exit, required text, env...
  local name=$1 want=$2 text=$3; shift 3
  env "$@" SOLAR_DIR="$SOLAR_DIR" bash "$here/verify_binding.sh" > "$t/$name.out" 2>&1; local st=$?
  local msg; msg=$(grep -m1 '^BINDING FAILED' "$t/$name.out")
  if [[ $st == "$want" && $msg == *"$text"* ]]; then r=pass; else r=FAIL; ok=1; fi
  echo "$r $name exit $st: $msg"
}
# Altered source byte: the first byte of the flattened file.
python3 -I -c 'import sys; b=bytearray(open(sys.argv[1],"rb").read()); b[0]^=1; open(sys.argv[2],"wb").write(b)' "$src" "$t/src.sol"
run source 2 "pin source:" SRC="$t/src.sol"
# Altered options: -Osize for -Ogas.
sed 's/^-Ogas$/-Osize/' "$root/Certified/uv2_erc20/options" > "$t/options"
run options 2 "pin options:" OPTIONS="$t/options"
# Another solc binary: the pinned one with one byte appended.
cp "$root/.cache/solc-0.8.35" "$t/solc"; printf '\0' >> "$t/solc"
run solc 2 "pin solc:" SOLC="$t/solc"
# Another emitter binary: the pinned one with one byte appended.
cp "$solar" "$t/solar"; printf '\0' >> "$t/solar"
run emitter 2 "pin emitter:" SOLAR="$t/solar"
# Another spec exporter binary.
cp "$sv" "$t/solar-verify"; printf '\0' >> "$t/solar-verify"
run spec-exporter 2 "pin spec-exporter:" SOLAR_VERIFY="$t/solar-verify"
# Pins intact, the statement's runtime bytes changed: a copy of the checkout with byte 0 of
# runtimeBytes altered.
mk() { rm -rf "$t/co"; mkdir -p "$t/co"; (cd "$root" && tar cf - Certified/uv2_transfer_e6 Certified/uv2_erc20/options Certified/uv2_erc20/gen scripts/solc_ast_to_lean_source.py scripts/harness_cache.py scripts/verify/uniswap_v2_sources.py scripts/verify/uniswap-v2/UniswapV2ERC20.sol Contracts/UniswapV2/ERC20/Source.lean Contracts/UniswapV2/ERC20/Slice/Gen/Spec.lean) | tar xf - -C "$t/co"; }
co_run() {  # name, text
  env SOLAR_DIR="$SOLAR_DIR" SOLC="$root/.cache/solc-0.8.35" SOLAR="$solar" bash "$t/co/Certified/uv2_transfer_e6/verify_binding.sh" > "$t/$1.out" 2>&1; local st=$?
  local msg; msg=$(grep -m1 '^BINDING FAILED' "$t/$1.out")
  if [[ $st == 1 && $msg == *"$2"* ]]; then r=pass; else r=FAIL; ok=1; fi
  echo "$r $1 exit $st: $msg"
}
# Control: the unaltered copy binds (exit 0), so each copy control fails only by its alteration.
mk; env SOLAR_DIR="$SOLAR_DIR" SOLC="$root/.cache/solc-0.8.35" SOLAR="$solar" bash "$t/co/Certified/uv2_transfer_e6/verify_binding.sh" > "$t/copy.out" 2>&1; st=$?
if [[ $st == 0 ]]; then echo "pass copy-unaltered exit 0: $(tail -1 "$t/copy.out" | cut -d';' -f1)"; else echo "FAIL copy-unaltered exit $st"; ok=1; fi
mk; L=$(grep -n 'def runtimeBytes' "$t/co/Certified/uv2_transfer_e6/Statement.lean" | cut -d: -f1)
sed -i "$((L + 1))s/^  96,/  97,/" "$t/co/Certified/uv2_transfer_e6/Statement.lean"
co_run runtime-bytes "runtime bytes differ"
mk; echo "-- altered" >> "$t/co/Certified/uv2_erc20/gen/UniswapV2ERC20/Mir2.lean"
co_run stage "stage Mir2.lean differs"
mk; sed -i '0,/importedSourceUnit/s//importedSourceUnit/' "$t/co/Contracts/UniswapV2/ERC20/Source.lean"; echo "-- altered" >> "$t/co/Contracts/UniswapV2/ERC20/Source.lean"
co_run import "import: imported source differs"
mk; echo "-- altered" >> "$t/co/Contracts/UniswapV2/ERC20/Slice/Gen/Spec.lean"
co_run spec "spec export differs"
exit $ok
