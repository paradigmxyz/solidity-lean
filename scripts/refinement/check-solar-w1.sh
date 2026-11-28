#!/usr/bin/env bash
# Check that the runtime bytecode literal of SolidCore/Refinement/Solar/W1.lean is what solar
# emits for the milestone contract w1, by sha256, and that the recorded sha256 is the literal's.
#
#   scripts/refinement/check-solar-w1.sh [path/to/solar] [path/to/w1.sol]
#
# solar must be built at the commit the Lean file names (c7ac11c0); the script prints the
# compiler's version line and fails on any mismatch.
set -euo pipefail
cd "$(dirname "$0")/../.."

solar=${1:?usage: check-solar-w1.sh SOLAR W1_SOL}
source=${2:?usage: check-solar-w1.sh SOLAR W1_SOL}
lean=SolidCore/Refinement/Solar/W1.lean

literal=$(sed -n '/^def runtimeHex/{n;s/.*"\([0-9a-f]*\)".*/\1/p}' "$lean")
recorded=$(sed -n 's/^def runtimeSha256 : String := "\([0-9a-f]*\)"/\1/p' "$lean")
"$solar" --version | head -1
emitted=$("$solar" "$source" -Ogas --evm-version osaka --emit=bin-runtime 2>/dev/null |
  python3 -c 'import json,sys; c=json.load(sys.stdin)["contracts"]; print(next(v["bin-runtime"] for k,v in c.items() if k.endswith(":Main")))')

sha() { python3 -c 'import hashlib,sys; print(hashlib.sha256(bytes.fromhex(sys.argv[1])).hexdigest())' "$1"; }
lit_sha=$(sha "$literal")
out_sha=$(sha "$emitted")
echo "literal  sha256 $lit_sha"
echo "recorded sha256 $recorded"
echo "solar    sha256 $out_sha"
[[ "$lit_sha" == "$recorded" ]] || { echo "recorded sha256 is not the literal's" >&2; exit 1; }
[[ "$lit_sha" == "$out_sha" ]] || { echo "the literal is not solar's output" >&2; exit 1; }
nat=$(sed -n '/^def runtimeNat/{n;s/^ *0x\([0-9a-f]*\)$/\1/p}' "$lean")
[[ "$nat" == "$literal" ]] || { echo "runtimeNat is not runtimeHex" >&2; exit 1; }
echo "ok: the Lean literal is solar's runtime bytecode for w1"
