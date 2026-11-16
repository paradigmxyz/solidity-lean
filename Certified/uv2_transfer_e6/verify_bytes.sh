#!/bin/bash
# Re-emit UniswapV2ERC20's runtime bytecode with the pinned solar and options, and check it equals
# runtimeBytes in Statement.lean. Exit 0 on equality, 1 on any difference.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
solar=${SOLAR:-$root/.cache/solar-stages/target/release/solar}
mapfile -t opts < "$root/Certified/uv2_erc20/options"
out=$(cd "$root/scripts/verify/uniswap-v2" && "$solar" "${opts[@]}" --emit bin-runtime UniswapV2ERC20.sol)
python3 - "$root/Certified/uv2_transfer_e6/Statement.lean" <<EOF
import json, re, sys
j = json.loads('''$out''')
hexs = [v["bin-runtime"] for k, v in j["contracts"].items() if k.endswith(":UniswapV2ERC20")]
assert len(hexs) == 1, "expected one UniswapV2ERC20"
fresh = list(bytes.fromhex(hexs[0]))
s = open(sys.argv[1]).read()
m = re.search(r"def runtimeBytes : List Nat := \[([0-9,\s]*)\]", s)
lit = [int(x) for x in m.group(1).replace("\n", " ").split(",")]
print(f"fresh {len(fresh)} bytes, statement {len(lit)} bytes, equal {fresh == lit}")
sys.exit(0 if fresh == lit else 1)
EOF
