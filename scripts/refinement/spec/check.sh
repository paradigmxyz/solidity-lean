#!/usr/bin/env bash
# Check the specs solar-verify exported for the spec corpus (scripts/refinement/spec).
#
#   SOLAR_VERIFY=path/to/solar-verify scripts/refinement/spec/check.sh
#
# For each annotated source NAME.sol it
#   1. regenerates SolidCore/Spec/Export/<Module>.lean with solar-verify --emit-lean and fails if it
#      differs from the checked-in file;
#   2. checks that the annotated source is the corpus source it annotates
#      (scripts/refinement/corpus/c4.sol) with comments and whitespace removed, so the compiler
#      sees the same program;
#   3. checks that the manifest's bytecode sha256 is the sha256 of the runtime bytecode the corpus
#      refinement is about (SolidCore/Refinement/Bytecode/C4.lean).
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/../../.."

sv="${SOLAR_VERIFY:?set SOLAR_VERIFY to a solar-verify binary with --emit-lean}"
compiler="solar 0.3.0-dev+commit.9688f215"
sha="8a21bc207d9dd8be48d921a717eda3ecb7e5bfcb5397850bc3d64a29037fac47"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

for pair in c4:C4 c4_wrong:C4Wrong; do
  name="${pair%%:*}"
  mod="${pair##*:}"
  "$sv" "scripts/refinement/spec/$name.sol" --emit-lean "$tmp/$mod.lean" \
    --lean-module "SolidCore.Spec.Export.$mod" --lean-compiler "$compiler" \
    --lean-bytecode-sha256 "$sha"
  diff -u "SolidCore/Spec/Export/$mod.lean" "$tmp/$mod.lean"
done

strip() { sed -e 's|//.*$||' "$1" | tr -d ' \t\n'; }
[[ "$(strip scripts/refinement/spec/c4.sol)" == "$(strip scripts/refinement/corpus/c4.sol)" ]] || {
  echo "spec/c4.sol is not corpus/c4.sol with comments" >&2
  exit 1
}

python3 - "$sha" <<'PY'
import hashlib, re, sys
s = open("SolidCore/Refinement/Bytecode/C4.lean").read()
h = re.search(r"def Main.runtimeNat : Nat :=\s*0x([0-9a-f]+)", s).group(1)
n = int(re.search(r"runtimeSize : Nat := (\d+)", s).group(1))
got = hashlib.sha256(bytes.fromhex(h.rjust(2 * n, "0"))).hexdigest()
if got != sys.argv[1]:
    sys.exit(f"bytecode sha256 {got} is not the manifest's {sys.argv[1]}")
PY
echo "spec exports, sources and bytecode hash check out"
