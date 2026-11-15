#!/usr/bin/env bash
# Prepare a fresh Linux box as a solidity-lean build worker: system packages, elan with the
# repository's pinned toolchain, a checkout of one commit and Mathlib's prebuilt cache.
#
#   tools/pool/bootstrap.sh <full-sha|branch> [--dir DIR] [--with-rust] [--no-cache]
#
# DIR defaults to $POOL_ROOT/solidity-lean ($POOL_ROOT defaults to ~/pool). Re-running on the same
# DIR moves it to the new commit and keeps .lake, so a lane can build commit after commit.
# --with-rust installs a Rust toolchain (rustup, stable), which build.sh's ci-gen set needs to
# build solar for the generated Uniswap V2 modules. Prints the checkout's path on stdout.
source "$(dirname "${BASH_SOURCE[0]}")/common.sh"

ref="" dir="" with_rust=0 cache=1
while (( $# )); do
  case "$1" in
    --dir) dir="$2"; shift 2 ;;
    --with-rust) with_rust=1; shift ;;
    --no-cache) cache=0; shift ;;
    -h|--help) sed -n '2,12p' "$0"; exit 0 ;;
    *) [[ -z "$ref" ]] || pool_die "unexpected argument $1"; ref="$1"; shift ;;
  esac
done
[[ -n "$ref" ]] || pool_die "usage: bootstrap.sh <full-sha|branch> [--dir DIR] [--with-rust] [--no-cache]"
dir="${dir:-$POOL_ROOT/solidity-lean}"
t0=$(date +%s)

# System packages: git and curl for the checkout and caches, zstd for pack.sh, GNU time for
# per-step peak RSS, python3 for the CI step parser and the generators, unzip for the proof
# checks' tool downloads (scripts/refinement/facts.sh).
need=()
for c in git curl zstd python3 cc make unzip; do command -v "$c" >/dev/null || need+=("$c"); done
[[ -x /usr/bin/time ]] || need+=(time)
if (( ${#need[@]} )); then
  pool_log "installing system packages (missing: ${need[*]})"
  sudo DEBIAN_FRONTEND=noninteractive apt-get update -qq
  sudo DEBIAN_FRONTEND=noninteractive apt-get install -y -qq git curl zstd python3 build-essential time unzip >/dev/null
fi

if ! command -v elan >/dev/null; then
  pool_log "installing elan"
  curl -fsSL -o /tmp/elan-init.sh "$POOL_ELAN_INIT"
  sh /tmp/elan-init.sh -y --default-toolchain none >/dev/null
  rm -f /tmp/elan-init.sh
fi

if (( with_rust )) && ! command -v cargo >/dev/null; then
  pool_log "installing Rust"
  curl -fsSL https://sh.rustup.rs | sh -s -- -y --profile minimal --default-toolchain stable >/dev/null
fi

pool_log "checking out $ref into $dir"
mkdir -p "$dir"
if [[ ! -d "$dir/.git" ]]; then
  git init -q "$dir"
  git -C "$dir" remote add origin "$POOL_REPO_URL"
fi
# GitHub serves a commit by its full SHA; a short SHA must be given as a branch instead.
git -C "$dir" fetch -q --depth 1 origin "$ref" || pool_die "cannot fetch $ref (give a full 40-character SHA or a branch)"
git -C "$dir" checkout -q --force --detach FETCH_HEAD
sha="$(git -C "$dir" rev-parse HEAD)"
pool_log "at $sha"

cd "$dir"
toolchain="$(tr -d '[:space:]' < lean-toolchain)"
pool_log "installing $toolchain"
if ! elan toolchain install "$toolchain" >/dev/null 2>&1; then
  # elan's own resolver may not expand a proxy's short cluster name (a.b.svc); retry with the
  # proxy's address.
  proxy="${HTTPS_PROXY:-${https_proxy:-}}"
  host="$(sed -E 's#^[a-z]+://([^@/]*@)?([^:/]+).*#\2#' <<< "$proxy")"
  ip="$(getent hosts "$host" 2>/dev/null | awk '{print $1; exit}')"
  [[ -n "$proxy" && -n "$ip" ]] || pool_die "elan could not install $toolchain"
  p="${proxy/$host/$ip}"
  HTTPS_PROXY="$p" https_proxy="$p" HTTP_PROXY="$p" http_proxy="$p" elan toolchain install "$toolchain" >/dev/null \
    || pool_die "elan could not install $toolchain"
fi
elan override set "$toolchain" >/dev/null

if (( cache )); then
  pool_log "fetching Mathlib's cache (lake exe cache get)"
  tc=$(date +%s)
  mkdir -p .lake
  lake exe cache get >/dev/null 2>.lake/pool-cache-get.log || pool_log "cache get failed (see .lake/pool-cache-get.log); the build will compile Mathlib"
  pool_log "cache get took $(( $(date +%s) - tc ))s"
fi
pool_log "bootstrap of $sha took $(( $(date +%s) - t0 ))s"
echo "$dir"
