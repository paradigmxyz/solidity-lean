#!/usr/bin/env bash
# Regenerate solar-verify's exported transcripts and fail if any changed.
#
#   SOLAR_VERIFY=/path/to/solar-verify scripts/verify/check.sh
#
# For each scripts/verify/NAME.sol (a copy of solar's crates/verify/examples/NAME.sol), runs
# solar-verify --dry-run with --dump-smt and --dump-lean, compares the Lean module with
# SolidCore/Verify/VC/Export/NAME.lean, and the source's and transcript's SHA-256 with
# scripts/verify/MANIFEST. lake build SolidCoreVerifyVC then checks (SolidCore/Verify/VC/Bind.lean)
# that each script prints back to its transcript.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/../.."
: "${SOLAR_VERIFY:?set SOLAR_VERIFY to a solar-verify binary built with --dump-lean}"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
status=0
for sol in scripts/verify/*.sol; do
  name="$(basename "$sol" .sol)"
  # A dry run proves nothing, so solar-verify exits 1; 2 is an error.
  rc=0
  "$SOLAR_VERIFY" --dry-run --dump-smt "$tmp/$name.smt2" --dump-lean "$tmp/$name.lean" \
    --lean-namespace "SolidCore.Verify.VC.Export.$name" "$sol" > /dev/null 2> "$tmp/$name.err" || rc=$?
  if [[ $rc -gt 1 ]]; then cat "$tmp/$name.err" >&2; exit "$rc"; fi
  if ! cmp -s "$tmp/$name.lean" "SolidCore/Verify/VC/Export/$name.lean"; then
    echo "error: SolidCore/Verify/VC/Export/$name.lean differs from solar-verify's export" >&2
    status=1
  fi
  for f in "$sol" "$tmp/$name.smt2"; do
    want="$(grep " $(basename "$f")\$" scripts/verify/MANIFEST | cut -d' ' -f1)"
    got="$(sha256sum "$f" | cut -d' ' -f1)"
    if [[ "$want" != "$got" ]]; then
      echo "error: $(basename "$f"): sha256 $got, MANIFEST says ${want:-nothing}" >&2
      status=1
    fi
  done
done
exit "$status"
