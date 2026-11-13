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
# Annotated copies of sources the refinement certifies: stripping the NatSpec lines must give
# the certified source back byte for byte.
if ! grep -v '^ *///' scripts/verify/CounterMilestone.sol | cmp -s - scripts/refinement/counter/counter.sol; then
  echo "error: scripts/verify/CounterMilestone.sol is not scripts/refinement/counter/counter.sol plus NatSpec" >&2
  status=1
fi
check() { # check DIR NAMESPACE_PREFIX EXPORT_DIR
  local dir="$1" ns="$2" out="$3" sol name rc f want got
  for sol in "$dir"/*.sol; do
    name="$(basename "$sol" .sol)"
    # A dry run proves nothing, so solar-verify exits 1; 2 is an error.
    rc=0
    "$SOLAR_VERIFY" --dry-run --dump-smt "$tmp/$name.smt2" --dump-lean "$tmp/$name.lean" \
      --lean-namespace "$ns.$name" "$sol" > /dev/null 2> "$tmp/$name.err" || rc=$?
    if [[ $rc -gt 1 ]]; then cat "$tmp/$name.err" >&2; exit "$rc"; fi
    if ! cmp -s "$tmp/$name.lean" "$out/$name.lean"; then
      echo "error: $out/$name.lean differs from solar-verify's export" >&2
      status=1
    fi
    # A function outside the Lean fragment is left raw: refused, never checked.
    grep '^-- Left raw' "$tmp/$name.lean" | sed "s|^-- Left raw, outside the Lean fragment: |refused ($name): |" >&2 || true
    for f in "$sol" "$tmp/$name.smt2"; do
      want="$(grep " $(basename "$f")\$" "$dir/MANIFEST" | cut -d' ' -f1)"
      got="$(sha256sum "$f" | cut -d' ' -f1)"
      if [[ "$want" != "$got" ]]; then
        echo "error: $(basename "$f"): sha256 $got, $dir/MANIFEST says ${want:-nothing}" >&2
        status=1
      fi
    done
  done
}
check scripts/verify SolidCore.Verify.VC.Export SolidCore/Verify/VC/Export
check scripts/verify/mutant SolidCore.Verify.VC.Export.Mutant SolidCore/Verify/VC/Export/Mutant
exit "$status"
