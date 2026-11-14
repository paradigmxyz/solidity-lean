#!/usr/bin/env bash
# Regenerate solar-verify's exports and fail if any changed.
#
#   SOLAR_VERIFY=/path/to/solar-verify scripts/verify/check.sh
#
# For each scripts/verify/NAME.sol (a copy of solar's crates/verify/examples/NAME.sol, or an
# annotated copy of a source the refinement certifies) and each mutant in scripts/verify/mutant,
# runs solar-verify --dry-run with --dump-smt and --dump-lean, compares the Lean module with its
# file under Contracts/ (out_of), and the source's and transcript's SHA-256 with the MANIFEST.
# lake build ContractsVC then checks (Contracts/NAME/VC/Bind.lean) that each script prints back to
# its transcript. It also compares solar-verify's spec exports (--emit-lean-spec) with
# Contracts/Counter/Spec/{Export,ExportWrong}.lean (spec_of).
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/../.."
: "${SOLAR_VERIFY:?set SOLAR_VERIFY to a solar-verify binary built with --dump-lean and --emit-lean-spec}"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
status=0
# Annotated copies of sources the refinement certifies: stripping the NatSpec lines must give
# the certified source back byte for byte.
if ! grep -v '^ *///' scripts/verify/CounterMilestone.sol | cmp -s - scripts/refinement/counter/counter.sol; then
  echo "error: scripts/verify/CounterMilestone.sol is not scripts/refinement/counter/counter.sol plus NatSpec" >&2
  status=1
fi
# Token's certified backend (Certified/verify_token) compiles this Token: the same bytes, and the
# source hash its stage manifest records is the one MANIFEST pins.
if ! cmp -s scripts/verify/Token.sol Certified/verify_token/verify_token.sol; then
  echo "error: Certified/verify_token/verify_token.sol is not scripts/verify/Token.sol" >&2
  status=1
fi
token_sha="$(grep ' Token.sol$' scripts/verify/MANIFEST | cut -d' ' -f1)"
if ! grep -qF "\"$token_sha\")]" Certified/verify_token/gen/Token/Manifest.lean; then
  echo "error: Certified/verify_token's stage manifest records no source with sha256 $token_sha" >&2
  status=1
fi
# The Lean module of each transcript.
out_of() {
  case "$1" in
    CounterMilestone) echo Contracts/Counter/VC/ExportMilestone.lean ;;
    CounterSrcMut) echo Contracts/Counter/VC/Mutant/SrcMut.lean ;;
    CounterSpecMut) echo Contracts/Counter/VC/Mutant/SpecMut.lean ;;
    TokenSrcMut) echo Contracts/Token/VC/Mutant/SrcMut.lean ;;
    TokenSpecMut) echo Contracts/Token/VC/Mutant/SpecMut.lean ;;
    *) echo "Contracts/$1/VC/Export.lean" ;;
  esac
}
check() { # check DIR NAMESPACE_PREFIX
  local dir="$1" ns="$2" sol name rc f want got out
  for sol in "$dir"/*.sol; do
    name="$(basename "$sol" .sol)"
    out="$(out_of "$name")"
    # A dry run proves nothing, so solar-verify exits 1; 2 is an error.
    rc=0
    "$SOLAR_VERIFY" --dry-run --dump-smt "$tmp/$name.smt2" --dump-lean "$tmp/$name.lean" \
      --lean-namespace "$ns.$name" "$sol" > /dev/null 2> "$tmp/$name.err" || rc=$?
    if [[ $rc -gt 1 ]]; then cat "$tmp/$name.err" >&2; exit "$rc"; fi
    # The export imports the library by its module path in this repository.
    sed -i 's/^import SolidCore\.Verify\.VC\.Term$/import Verify.VC.Term/' "$tmp/$name.lean"
    if ! cmp -s "$tmp/$name.lean" "$out"; then
      echo "error: $out differs from solar-verify's export" >&2
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
check scripts/verify SolidCore.Verify.VC.Export
check scripts/verify/mutant SolidCore.Verify.VC.Export.Mutant
# solar-verify's spec exports, bound to the counter milestone's compiler and bytecode
# (solar-tv/milestone/counter's manifest).
counter_compiler="0.8.38+commit.1134e61f.solar.0.3.0-dev"
counter_bytecode="daed21b0c790bb2c08bcf999c9ebc6fea950c213ea0a799418552aa14c18f6ec"
spec_of() { # spec_of SOURCE MODULE OUT
  rm -f "$tmp/spec.lean"
  "$SOLAR_VERIFY" --dry-run --emit-lean-spec "$tmp/spec.lean" --lean-spec-module "$2" \
    --lean-spec-compiler "$counter_compiler" --lean-spec-bytecode-sha256 "$counter_bytecode" \
    "$1" > /dev/null 2> "$tmp/spec.err" || true
  if [[ ! -s "$tmp/spec.lean" ]]; then
    cat "$tmp/spec.err" >&2
    echo "error: solar-verify wrote no spec export for $1" >&2
    status=1
    return
  fi
  sed -i 's/^import SolidCore\.Spec\.Contract$/import Verify.Spec.Contract/' "$tmp/spec.lean"
  if ! cmp -s "$tmp/spec.lean" "$3"; then
    echo "error: $3 differs from solar-verify's spec export" >&2
    diff "$tmp/spec.lean" "$3" >&2 || true
    status=1
  fi
}
spec_of scripts/verify/CounterMilestone.sol SolidCore.Spec.Export.Counter Contracts/Counter/Spec/Export.lean
spec_of scripts/verify/mutant/CounterSpecMut.sol SolidCore.Spec.Export.CounterSpecMut \
  Contracts/Counter/Spec/ExportWrong.lean
exit "$status"
