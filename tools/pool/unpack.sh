#!/usr/bin/env bash
# Restore a pack.sh archive onto a checkout of the same commit, then let lake confirm it is warm.
#
#   tools/pool/unpack.sh FILE [--dir DIR] [--force]
#
# Refuses a pack made at a different lake-manifest.json or lean-toolchain (dependency outputs would
# not match); a pack from another commit of the project is allowed (lake rebuilds what changed).
# --force skips the check.
source "$(dirname "${BASH_SOURCE[0]}")/common.sh"
file="" dir="" force=0
while (( $# )); do
  case "$1" in
    --dir) dir="$2"; shift 2 ;;
    --force) force=1; shift ;;
    -h|--help) sed -n '2,9p' "$0"; exit 0 ;;
    *) file="$1"; shift ;;
  esac
done
[[ -f "$file" ]] || pool_die "usage: unpack.sh FILE [--dir DIR]"
dir="${dir:-$POOL_ROOT/solidity-lean}"
cd "$dir"
meta="$(zstd -dc "$file" | tar -xOf - .lake/pool-pack.meta)"
want="$(sha256sum lake-manifest.json lean-toolchain | awk '{print $1}' | tr '\n' ' ')"
if [[ "$(sed -n 2p <<< "$meta")" != "$want" ]] && (( ! force )); then
  pool_die "pack was made at another lake-manifest.json or lean-toolchain (pack commit $(head -n1 <<< "$meta")); use --force to restore anyway"
fi
t0=$(date +%s)
zstd -dc -T0 "$file" | tar -C "$dir" -xf -
pool_log "restored pack of $(head -n1 <<< "$meta") into $dir in $(( $(date +%s) - t0 ))s"
