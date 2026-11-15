# Shared settings for tools/pool. Sourced, not run.
# shellcheck shell=bash
set -euo pipefail

POOL_REPO_URL="${POOL_REPO_URL:-https://github.com/paradigmxyz/solidity-lean.git}"
POOL_ROOT="${POOL_ROOT:-$HOME/pool}"
# The elan installer CI pins (.github/workflows/refinement.yml).
POOL_ELAN_INIT="https://raw.githubusercontent.com/leanprover/elan/227caca133724d5516bee25c2aeb3e609478f2d8/elan-init.sh"
export PATH="$HOME/.elan/bin:$HOME/.cargo/bin:$PATH"

pool_log() { printf '[pool %s] %s\n' "$(date -u +%H:%M:%S)" "$*" >&2; }
pool_die() { pool_log "error: $*"; exit 1; }

# Memory in GB the machine has (MemTotal).
pool_mem_gb() { awk '/MemTotal/ {printf "%d", $2/1048576}' /proc/meminfo; }

# Default worker count: one per CPU, but at most one per 5 GB of RAM (the heaviest CI modules
# peak near 6 GB, most far below).
pool_default_threads() {
  local cpus mem
  cpus="$(nproc)"; mem="$(pool_mem_gb)"
  local by_mem=$(( mem / 5 )); (( by_mem < 1 )) && by_mem=1
  (( cpus < by_mem )) && echo "$cpus" || echo "$by_mem"
}

# Samples system-wide used memory (MemTotal - MemAvailable) every second into $1 until killed,
# keeping only the peak in KiB.
pool_mem_sampler() {
  local out="$1" peak=0 used
  while :; do
    used="$(awk '/MemTotal/ {t=$2} /MemAvailable/ {a=$2} END {print t-a}' /proc/meminfo)"
    (( used > peak )) && { peak="$used"; echo "$peak" > "$out"; }
    sleep 1
  done
}

pool_gib() { awk -v k="$1" 'BEGIN {printf "%.1f", k/1048576}'; }
