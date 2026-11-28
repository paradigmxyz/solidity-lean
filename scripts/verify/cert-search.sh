#!/usr/bin/env bash
# Usage: cert-search.sh IMPORT SCRIPT OUT OBS [MASK]
# Writes OUT/certs/ob<i>.txt for each obligation index in OBS (comma-separated) that the search
# certifies; scripts/verify/gen-certified.py turns OUT/certs into kernel-checked modules.
set -eu
imp="$1"; script="$2"; out="$3"; obs="$4"; mask="${5-}"
mkdir -p "$out/certs"
f=$(mktemp --suffix=.lean -p "$out")
sed -e "s|@IMPORT@|$imp|" -e "s|@SCRIPT@|$script|" "$(dirname "$0")/cert-search.lean.in" > "$f"
if [ -n "$mask" ]; then export MASK="$mask"; fi
OUT="$out" OBS="$obs" lake env lean "$f"
rm -f "$f"
