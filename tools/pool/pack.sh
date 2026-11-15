#!/usr/bin/env bash
# Pack a worker's build outputs so another lane can start warm.
#
#   tools/pool/pack.sh [--dir DIR] [--out FILE] [--scope all|project]
#
# all (default): the whole .lake (dependency checkouts and their builds, Mathlib's oleans and
#   the project's build), enough to restore onto a bare checkout of the same commit.
# project: only .lake/build (this repository's own outputs), for a lane that already ran
#   bootstrap.sh (dependencies and Mathlib's cache) at the same lake-manifest.json.
# Generated GPL-3.0 sources stay out (they live outside .lake); their compiled outputs are inside
# .lake/build: keep packs on Tempo's workers, never publish them.
# Writes FILE (default $POOL_ROOT/packs/<sha12>-<scope>.tar.zst) with zstd -T0 and prints its size.
source "$(dirname "${BASH_SOURCE[0]}")/common.sh"
dir="" out="" scope=all
while (( $# )); do
  case "$1" in
    --dir) dir="$2"; shift 2 ;;
    --out) out="$2"; shift 2 ;;
    --scope) scope="$2"; shift 2 ;;
    -h|--help) sed -n '2,13p' "$0"; exit 0 ;;
    *) pool_die "unexpected argument $1" ;;
  esac
done
dir="${dir:-$POOL_ROOT/solidity-lean}"
cd "$dir"
sha="$(git rev-parse HEAD)"
case "$scope" in
  all) paths=(.lake) ;;
  project) paths=(.lake/build) ;;
  *) pool_die "scope must be all or project" ;;
esac
out="${out:-$POOL_ROOT/packs/${sha:0:12}-$scope.tar.zst}"
mkdir -p "$(dirname "$out")"
printf '%s\n%s\n' "$sha" "$(sha256sum lake-manifest.json lean-toolchain | awk '{print $1}' | tr '\n' ' ')" > .lake/pool-pack.meta
t0=$(date +%s)
raw=$(du -sb "${paths[@]}" | awk '{s+=$1} END {print s}')
tar -C "$dir" --exclude='.lake/pool-step.time' -cf - "${paths[@]}" .lake/pool-pack.meta | zstd -q -T0 -3 -o "$out" -f
size=$(stat -c %s "$out")
pool_log "packed $scope of $sha: $(awk -v b="$raw" 'BEGIN {printf "%.2f", b/1073741824}') GiB raw -> $(awk -v b="$size" 'BEGIN {printf "%.2f", b/1073741824}') GiB in $(( $(date +%s) - t0 ))s"
echo "$out"
