#!/usr/bin/env bash
# Kernel discharge of solar-verify's verification conditions for the Uniswap V2 port.
#
#   Contracts/UniswapV2/VC/discharge.sh SOLAR_ROOT SOLAR_VERIFY OUT [CONTRACT...]
#
# SOLAR_ROOT is a solar checkout (paradigmxyz/solar) with solar-tv/uniswap-v2/port.py and
# crates/verify/uniswap-v2/{apply_specs.py,uniswap-v2.spec}; SOLAR_VERIFY its solar-verify binary.
# v2-core is GPL-3.0, so this repository keeps neither the port nor its exports: the script writes
# the port (port.py clones v2-core at the pinned commit), applies the specs, exports every query
# with 'solar-verify --emit-lean' (manifest version 2) and runs Verify/Discharge/discharge.sh on
# each export, all under OUT. CONTRACT is Math, Factory, ERC20 or Pair (default: all four).
#
# Each OUT/vcs/<C>/discharge/{results,summary}.tsv is the per-row verdict, with the axioms of every
# proof and the vacuity column; the run fails unless every required obligation of every contract
# is proved by a proof whose axioms are propext, Classical.choice and Quot.sound.
#
# Environment: UV2_TIMEOUT_MS (solar-verify's per-query timeout, default 120000; Pair.swap needs
# it), UV2_LEAN_TIMEOUT (seconds per Lean attempt, default 120), and discharge.sh's DISCHARGE_*.
set -euo pipefail
solar=$(cd "$1" && pwd)
verifier=$(realpath "$2")
mkdir -p "$3"
out=$(cd "$3" && pwd)
shift 3
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
contracts=("$@")
[[ ${#contracts[@]} -gt 0 ]] || contracts=(Math Factory ERC20 Pair)
declare -A file=([Math]=libraries/Math.sol [Factory]=UniswapV2Factory.sol
  [ERC20]=UniswapV2ERC20.sol [Pair]=UniswapV2Pair.sol)

python3 "$solar/solar-tv/uniswap-v2/port.py" --v2-core "$out/v2-core" --out "$out/src"
rm -rf "$out/spec"
python3 "$solar/crates/verify/uniswap-v2/apply_specs.py" --src "$out/src" --out "$out/spec"

status=0
for c in "${contracts[@]}"; do
  f=${file[$c]:-}
  [[ -n $f ]] || { echo "error: unknown contract $c" >&2; exit 2; }
  rm -rf "$out/vcs/$c"
  # solar-verify exits 1 when a unit fails to verify or export; discharge.sh then fails closed on
  # the manifest, so the export's own status is reported but not trusted.
  (cd "$out/spec" && "$verifier" --timeout "${UV2_TIMEOUT_MS:-120000}" --emit-lean "$out/vcs/$c" "$f") \
    >"$out/vcs-$c.log" 2>&1 || echo "solar-verify: $c exited $?" >&2
  if DISCHARGE_SOURCE_ROOT="$out/spec" "$root/Verify/Discharge/discharge.sh" "$out/vcs/$c" \
      "${UV2_LEAN_TIMEOUT:-120}"; then
    echo "$c: every required obligation proved"
  else
    echo "$c: FAILED (see $out/vcs/$c/discharge/results.tsv)"
    status=1
  fi
done
exit $status
