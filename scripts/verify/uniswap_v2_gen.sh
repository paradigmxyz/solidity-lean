#!/usr/bin/env bash
# Generate SolidCore's Uniswap V2 sources before the build (they are not committed: v2-core is
# GPL-3.0, so this repository keeps the recipe, as solar keeps solar-tv/uniswap-v2/port.py).
#
#   scripts/verify/uniswap_v2_gen.sh
#
# Fetches paradigmxyz/solar at the commit in scripts/verify/uniswap-v2/solar-rev (only its
# sources: nothing is built; the refinement's scripts/refinement/solar-rev predates port.py),
# runs its solar-tv/uniswap-v2/port.py, which clones Uniswap/v2-core at the pinned commit and
# writes the ^0.8 port, then scripts/verify/uniswap_v2_sources.py and
# scripts/verify/uniswap_v2_core.py with solc 0.8.35 (downloaded and checked against its SHA-256
# unless SOLC names a binary). Fails if any generated module is missing afterwards, so a build
# never runs on stale or absent sources. SOLAR_DIR (default .cache/solar-uniswap-v2) is the checkout.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/../.."

rev="$(tr -d '[:space:]' < scripts/verify/uniswap-v2/solar-rev)"
solar_dir="${SOLAR_DIR:-.cache/solar-uniswap-v2}"
if [[ ! -d "$solar_dir/.git" ]]; then
  git init -q "$solar_dir"
  git -C "$solar_dir" remote add origin https://github.com/paradigmxyz/solar.git
fi
if [[ "$(git -C "$solar_dir" rev-parse -q --verify HEAD 2>/dev/null || true)" != "$rev" ]]; then
  git -C "$solar_dir" fetch -q --depth 1 origin "$rev"
  git -C "$solar_dir" checkout -q --detach "$rev"
fi

solc_version=0.8.35
solc_sha256=fa8ac9a32d301ad023a36ee5a29f8e291fe3200c60244e43c142539e82a617f4
if [[ -z "${SOLC-}" ]]; then
  SOLC=".cache/solc-$solc_version"
  if [[ ! -x "$SOLC" ]]; then
    mkdir -p .cache
    curl -fsSL -o "$SOLC.tmp" \
      "https://github.com/argotorg/solidity/releases/download/v$solc_version/solc-static-linux"
    echo "$solc_sha256  $SOLC.tmp" | sha256sum -c --quiet
    chmod +x "$SOLC.tmp"
    mv "$SOLC.tmp" "$SOLC"
  fi
fi

port=".cache/uniswap-v2/src"
python3 "$solar_dir/solar-tv/uniswap-v2/port.py" --out "$port" --v2-core .cache/uniswap-v2/v2-core
python3 scripts/verify/uniswap_v2_sources.py --port "$port" --solc "$SOLC"
python3 scripts/verify/uniswap_v2_core.py --solc "$SOLC"

status=0
for d in ERC20 Pair Factory; do
  for f in Source Core; do
    if [[ ! -s "Contracts/UniswapV2/$d/$f.lean" ]]; then
      echo "error: Contracts/UniswapV2/$d/$f.lean was not generated" >&2
      status=1
    fi
  done
done
if [[ ! -s "Contracts/UniswapV2/Pair/Contract.lean" ]]; then
  echo "error: Contracts/UniswapV2/Pair/Contract.lean was not generated" >&2
  status=1
fi
exit "$status"
