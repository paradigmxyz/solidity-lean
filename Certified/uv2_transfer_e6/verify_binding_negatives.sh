#!/bin/bash
# Negative controls for verify_binding.sh. Every control runs on a private copy of the inputs it
# reads and must stop before any comparison: each of the ten pins altered alone exits 2 naming that
# pin; the frozen replay manifest, the frozen binding receipt, or a file they name altered exits 3.
# The unaltered copy must exit 0. Prints one line per control; exits 0 iff every control does as
# required.
set -uo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
: "${SOLAR_DIR:?set SOLAR_DIR}"
t=$(mktemp -d); trap 'rm -rf "$t"' EXIT
solar=$root/.cache/solar-stages/target/release/solar
solc=$root/.cache/solc-0.8.35
sv=$SOLAR_DIR/target/release/solar-verify
ok=0
# A copy of everything the script reads in the checkout, and of the spec exporter's inputs.
mk() {
  rm -rf "$t/co" "$t/sd"; mkdir -p "$t/co" "$t/sd/crates/verify/uniswap-v2" "$t/sd/target/release"
  (cd "$root" && tar cf - Certified/uv2_transfer_e6 Certified/uv2_erc20/options scripts/solc_ast_to_lean_source.py \
    scripts/harness_cache.py scripts/verify/uniswap_v2_sources.py \
    $(awk '{print $2}' Certified/uv2_transfer_e6/GENERATED.sha256)) | tar xf - -C "$t/co"
  cp "$SOLAR_DIR/crates/verify/uniswap-v2/"{transfer-slice.spec,apply_specs.py} "$t/sd/crates/verify/uniswap-v2/"
  cp "$sv" "$t/sd/target/release/solar-verify"
}
run() {  # name, required exit, required text, env...
  local name=$1 want=$2 text=$3; shift 3
  env SOLAR_DIR="$t/sd" SOLC="$solc" SOLAR="$solar" "$@" bash "$t/co/Certified/uv2_transfer_e6/verify_binding.sh" > "$t/$name.out" 2>&1
  local st=$? msg
  msg=$(grep -m1 '^BINDING FAILED' "$t/$name.out")
  [[ $want == 0 ]] && msg=$(grep -m1 '^BOUND' "$t/$name.out" | cut -d';' -f1)
  if [[ $st == "$want" && $msg == *"$text"* ]] && ! grep -q '^runtime:' "$t/$name.out" || [[ $want == 0 && $st == 0 ]]; then
    r=pass; else r=FAIL; ok=1; fi
  echo "$r $name exit $st: $msg"
}
co=$t/co; flip0() { python3 -I -c 'import sys; p=sys.argv[1]; b=bytearray(open(p,"rb").read()); b[0]^=1; open(p,"wb").write(b)' "$1"; }

mk; run unaltered-copy 0 "BOUND"
# The ten pins, one at a time (exit 2, before any comparison).
mk; flip0 "$co/scripts/verify/uniswap-v2/UniswapV2ERC20.sol"; run pin-source 2 "pin source:"
mk; sed -i 's/^-Ogas$/-Osize/' "$co/Certified/uv2_erc20/options"; run pin-options 2 "pin options:"
mk; cp "$solc" "$t/solc"; printf '\0' >> "$t/solc"; run pin-solc 2 "pin solc:" SOLC="$t/solc"
mk; cp "$solar" "$t/solar"; printf '\0' >> "$t/solar"; run pin-emitter 2 "pin emitter:" SOLAR="$t/solar"
mk; printf '\0' >> "$t/sd/target/release/solar-verify"; run pin-spec-exporter 2 "pin spec-exporter:"
mk; printf '\n' >> "$t/sd/crates/verify/uniswap-v2/transfer-slice.spec"; run pin-spec 2 "pin spec:"
mk; printf '\n' >> "$t/sd/crates/verify/uniswap-v2/apply_specs.py"; run pin-spec-applier 2 "pin spec-applier:"
mk; printf '\n' >> "$co/scripts/solc_ast_to_lean_source.py"; run pin-importer 2 "pin importer:"
mk; printf '\n' >> "$co/scripts/harness_cache.py"; run pin-importer-cache 2 "pin importer-cache:"
mk; printf '\n' >> "$co/scripts/verify/uniswap_v2_sources.py"; run pin-import-driver 2 "pin import-driver:"
# The frozen manifests (exit 3, before any comparison).
mk; sed -i '1s/^./0/' "$co/Certified/uv2_transfer_e6/GENERATED.sha256"; run frozen-manifest 3 "frozen GENERATED.sha256:"
mk; sed -i 's/"result": "bound"/"result": "Bound"/' "$co/Certified/uv2_transfer_e6/binding.json"; run frozen-binding 3 "frozen binding.json:"
mk; rm "$co/Certified/uv2_erc20/gen/UniswapV2ERC20Mut/$(ls "$co/Certified/uv2_erc20/gen/UniswapV2ERC20Mut" | head -1)"; run frozen-generated-missing 3 "frozen generated file"
mk; echo "-- altered" >> "$co/Certified/uv2_erc20/gen/UniswapV2ERC20/Mir2.lean"; run frozen-stage 3 "frozen generated file Certified/uv2_erc20/gen/UniswapV2ERC20/Mir2.lean"
mk; echo "-- altered" >> "$co/Contracts/UniswapV2/ERC20/Source.lean"; run frozen-import 3 "frozen generated file Contracts/UniswapV2/ERC20/Source.lean"
mk; echo "-- altered" >> "$co/Contracts/UniswapV2/ERC20/Slice/Gen/Spec.lean"; run frozen-spec 3 "frozen generated file Contracts/UniswapV2/ERC20/Slice/Gen/Spec.lean"
mk; L=$(grep -n 'def runtimeBytes' "$co/Certified/uv2_transfer_e6/Statement.lean" | cut -d: -f1)
sed -i "$((L + 1))s/^  96,/  97,/" "$co/Certified/uv2_transfer_e6/Statement.lean"; run frozen-statement 3 "frozen binding.json statement_sha256"
# Coordinated drift: a stage module altered and both manifests rewritten to match it.
mk; f=Certified/uv2_erc20/gen/UniswapV2ERC20/Mir2.lean; echo "-- altered" >> "$co/$f"
n=$(cd "$co" && sha256sum "$f" | cut -c1-64)
python3 -I - "$co" "$f" "$n" <<'EOF'
import json, sys
co, f, n = sys.argv[1:]
g = f"{co}/Certified/uv2_transfer_e6/GENERATED.sha256"
lines = open(g).readlines()
new = [(n + "  " + l.split()[1] + "\n") if l.split()[1] == f else l for l in lines]
assert sum(a != b for a, b in zip(lines, new)) == 1
open(g, "w").write("".join(new))
b = f"{co}/Certified/uv2_transfer_e6/binding.json"; j = json.load(open(b)); j["stages"]["Mir2.lean"] = n
json.dump(j, open(b, "w"), indent=1, sort_keys=True)
EOF
run frozen-coordinated-drift 3 "frozen GENERATED.sha256:"
exit $ok
