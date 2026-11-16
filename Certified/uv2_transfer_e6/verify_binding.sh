#!/bin/bash
# Exact-input binding check for Certified/uv2_transfer_e6, failing closed.
#
# 1. Every pinned input (PINS) must have its recorded sha256 before anything runs; a mismatch exits
#    2 and names the pin.
# 2. The source's bytes are read once, into one private copy: the fresh emit, the stage export, the
#    AST import and the spec export all read that copy, whose sha256 is re-checked at the end.
# 3. The runtime bytes must equal Statement.lean's runtimeBytes, and the stage modules, the imported
#    source and the spec export must equal the committed generated files byte for byte; a difference
#    exits 1 and names the artifact.
# On success writes binding.json (every hash it checked) to $OUT (default: a temporary directory).
#
# Inputs, overridable to run the negative controls (the pins are not): SRC SOLC SOLAR OPTIONS
# (default: this checkout's), SOLAR_DIR (a solar checkout at the spec exporter's commit),
# SOLAR_VERIFY (default: $SOLAR_DIR/target/release/solar-verify).
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
here="$root/Certified/uv2_transfer_e6"
SRC=${SRC:-$root/scripts/verify/uniswap-v2/UniswapV2ERC20.sol}
SOLC=${SOLC:-$root/.cache/solc-0.8.35}
SOLAR=${SOLAR:-$root/.cache/solar-stages/target/release/solar}
OPTIONS=${OPTIONS:-$root/Certified/uv2_erc20/options}
: "${SOLAR_DIR:?set SOLAR_DIR to a solar checkout at the spec exporter commit}"
SOLAR_VERIFY=${SOLAR_VERIFY:-$SOLAR_DIR/target/release/solar-verify}
fail() { echo "BINDING FAILED: $1" >&2; exit "$2"; }
sha() { sha256sum "$1" | cut -c1-64; }

# 1. Pins.
declare -A path=(
  [source]=$SRC [options]=$OPTIONS [solc]=$SOLC [emitter]=$SOLAR [spec-exporter]=$SOLAR_VERIFY
  [spec]=$SOLAR_DIR/crates/verify/uniswap-v2/transfer-slice.spec
  [spec-applier]=$SOLAR_DIR/crates/verify/uniswap-v2/apply_specs.py
  [importer]=$root/scripts/solc_ast_to_lean_source.py
  [importer-cache]=$root/scripts/harness_cache.py
  [import-driver]=$root/scripts/verify/uniswap_v2_sources.py)
for name in "${!path[@]}"; do grep -q "^$name " "$here/PINS" || fail "pin $name not in PINS" 2; done
while read -r name want; do
  [[ -z $name || $name == \#* ]] && continue
  p=${path[$name]:-}
  [[ -n $p ]] || fail "pin $name unknown" 2
  [[ -f $p ]] || fail "pin $name: $p missing" 2
  got=$(sha "$p")
  [[ $got == "$want" ]] || fail "pin $name: sha256 $got, pinned $want ($p)" 2
done < "$here/PINS"
echo "pins: all ${#path[@]} match"

# 2. One private copy of the source.
tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
OUT=${OUT:-$tmp/out}; mkdir -p "$OUT" "$tmp/src"
cp "$SRC" "$tmp/src/UniswapV2ERC20.sol"
src_sha=$(sha "$tmp/src/UniswapV2ERC20.sol")
want_src=$(awk '$1 == "source" {print $2}' "$here/PINS")
[[ $src_sha == "$want_src" ]] || fail "pin source: copy differs" 2
mapfile -t opts < "$OPTIONS"

# Fresh emit and stage export, one run of the emitter.
(cd "$tmp/src" && "$SOLAR" "${opts[@]}" -Zemit-lean-stages="$tmp/stages" --emit bin-runtime UniswapV2ERC20.sol) \
  > "$tmp/emit.json" || fail "emit: solar exited nonzero" 1
python3 -I - "$tmp/emit.json" "$here/Statement.lean" "$tmp/runtime.hex" <<'EOF' || fail "runtime bytes differ from Statement.lean's runtimeBytes" 1
import json, re, sys
j = json.load(open(sys.argv[1]))
hexs = [v["bin-runtime"] for k, v in j["contracts"].items() if k.endswith(":UniswapV2ERC20")]
assert len(hexs) == 1
fresh = bytes.fromhex(hexs[0])
open(sys.argv[3], "w").write(hexs[0])
m = re.search(r"def runtimeBytes : List Nat := \[([0-9,\s]*)\]", open(sys.argv[2]).read())
lit = bytes(int(x) for x in m.group(1).split(","))
print(f"runtime: fresh {len(fresh)} bytes, statement {len(lit)} bytes, equal {fresh == lit}")
sys.exit(0 if fresh == lit else 1)
EOF
gen=$root/Certified/uv2_erc20/gen/UniswapV2ERC20
n=0
for f in "$gen"/*.lean; do
  b=$(basename "$f")
  # Manifest.lean records the export's source paths and output directory; no proof imports it.
  [[ $b == Manifest.lean ]] && continue
  cmp -s "$f" "$tmp/stages/UniswapV2ERC20/$b" || fail "stage $b differs from the fresh export" 1
  n=$((n + 1))
done
[[ $(ls "$tmp/stages/UniswapV2ERC20"/*.lean | wc -l) == $((n + 1)) ]] || fail "stage export has other modules" 1
echo "stages: $n modules equal the fresh export"

# AST import of the same copy (solc's AST, then the importer), into a private repository path.
set +e
python3 -I - "$root" "$SOLC" "$tmp/src/UniswapV2ERC20.sol" "$tmp/Source.lean" <<'EOF'

import importlib.util, pathlib, shutil, sys
root, solc, sol, out = pathlib.Path(sys.argv[1]), sys.argv[2], pathlib.Path(sys.argv[3]), sys.argv[4]
spec = importlib.util.spec_from_file_location("s", root / "scripts/verify/uniswap_v2_sources.py")
m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
# The driver names the source by a path inside the repository: stage the copy at a private one.
dst = root / "scripts/verify/uniswap-v2/.binding-UniswapV2ERC20.sol"
try:
    shutil.copyfile(sol, dst)
    try:
        text = m.lean_of(solc, dst, "UniswapV2ERC20", [])
    except Exception as e:
        print(f"importer: {e}", file=sys.stderr)
        sys.exit(3)
finally:
    dst.unlink(missing_ok=True)
# The module names the file read twice (its header and importedSourceName); the committed module
# names the flattened file, at this checkout's absolute path.
if text.count(".binding-UniswapV2ERC20.sol") != 2:
    sys.exit("import: unexpected source-name occurrences")
text = text.replace(".binding-UniswapV2ERC20.sol", "UniswapV2ERC20.sol")
# importedSourceName is solc's absolute path of the file: the generated module records the checkout
# it was imported in (RECORDED_ROOT). Only that string is normalized, and it must occur once.
RECORDED_ROOT = "/home/hand/wt/e6"
here_name = f'def importedSourceName : String := "{root}/scripts/verify/uniswap-v2/UniswapV2ERC20.sol"'
if text.count(here_name) != 1:
    sys.exit("import: importedSourceName not found")
text = text.replace(here_name, here_name.replace(str(root), RECORDED_ROOT, 1))
open(out, "w").write(text)
ok = text == (root / "Contracts/UniswapV2/ERC20/Source.lean").read_text()
print(f"import: equal {ok}")
sys.exit(0 if ok else 1)
EOF
st=$?; set -e
[[ $st == 0 ]] || { [[ $st == 1 ]] && fail "import: imported source differs from Contracts/UniswapV2/ERC20/Source.lean" 1; fail "import: the importer failed (exit $st)" 1; }

# Spec export of the same copy.
python3 -I "${path[spec-applier]}" --src "$tmp/src" --out "$tmp/plain" --spec "${path[spec]}" >/dev/null
(cd "$tmp/plain" && "$SOLAR_VERIFY" UniswapV2ERC20.sol --emit-lean-spec "$tmp/Spec.raw" \
  --lean-spec-module SolidCore.Spec.Export.UniswapV2ERC20Slice) || fail "spec export exited nonzero" 1
{ echo "-- Generated by scripts/verify/uniswap_v2_transfer_slice.sh. Do not edit."; cat "$tmp/Spec.raw"; } > "$tmp/Spec.lean"
cmp -s "$tmp/Spec.lean" "$root/Contracts/UniswapV2/ERC20/Slice/Gen/Spec.lean" || fail "spec export differs from Slice/Gen/Spec.lean" 1
echo "spec: equal True"

[[ $(sha "$tmp/src/UniswapV2ERC20.sol") == "$src_sha" ]] || fail "source copy changed during the run" 1
python3 -I - "$OUT/binding.json" "$src_sha" "$tmp" "$gen" "$root" "$here/PINS" <<'EOF'
import hashlib, json, pathlib, sys
out, src, tmp, gen, root, pins = sys.argv[1:]
h = lambda p: hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
r = {"result": "bound", "source_sha256": src,
     "pins": dict(l.split() for l in open(pins) if l.strip() and not l.startswith("#")),
     "runtime_hex_sha256": h(f"{tmp}/runtime.hex"),
     "emit_json_sha256": h(f"{tmp}/emit.json"),
     "stages": {p.name: h(p) for p in sorted(pathlib.Path(gen).glob("*.lean")) if p.name != "Manifest.lean"},
     "imported_source_sha256": h(f"{tmp}/Source.lean"),
     "spec_sha256": h(f"{tmp}/Spec.lean"),
     "statement_sha256": h(f"{root}/Certified/uv2_transfer_e6/Statement.lean")}
json.dump(r, open(out, "w"), indent=1, sort_keys=True)
EOF
echo "BOUND: source $src_sha; receipt $OUT/binding.json"
