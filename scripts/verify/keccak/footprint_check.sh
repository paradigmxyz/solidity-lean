#!/usr/bin/env bash
# Kernel check of one call's footprint premise for the real keccak256.
#
#   footprint_check.sh transfer     <balSlot> <caller> <to>
#   footprint_check.sh approve      <allowSlot> <caller> <spender>
#   footprint_check.sh transferFrom <balSlot> <allowSlot> <src> <dst> <caller>
#
# Slots are below 2^128, addresses below 2^160 (decimal or 0x hex). Writes a one-theorem Lean file,
# proves ScopedSep of the call's footprint by 'scopedSep_of_check (by decide +kernel)'
# (Verify/Spec/HashScopeCheck.lean), and checks its axioms. Prints the premise and exits 0 when the
# kernel accepts it; exits 1 when the check or the axiom audit fails, 2 on malformed input. Run from
# the repository root after 'lake build Verify.Spec.HashScopeCheck'.
set -euo pipefail

die() { echo "REFUSED $*" >&2; exit 2; }

num() { # num <value> <bits>: canonical decimal of a value below 2^bits, or refuse.
  python3 - "$1" "$2" <<'EOF' || exit 2
import sys
s, bits = sys.argv[1], int(sys.argv[2])
try:
    v = int(s, 16) if s.lower().startswith("0x") else int(s, 10)
except ValueError:
    sys.stderr.write(f"REFUSED not a number: {s}\n"); sys.exit(2)
if not (0 <= v < 2 ** bits):
    sys.stderr.write(f"REFUSED out of range (2^{bits}): {s}\n"); sys.exit(2)
print(v)
EOF
}

kind="${1:-}"; shift || true
case "$kind" in
  transfer)
    [ $# -eq 3 ] || die "transfer takes <balSlot> <caller> <to>"
    a=$(num "$1" 128); b=$(num "$2" 160); c=$(num "$3" 160)
    fp="transferFootprint $a $b $c" ;;
  approve)
    [ $# -eq 3 ] || die "approve takes <allowSlot> <caller> <spender>"
    a=$(num "$1" 128); b=$(num "$2" 160); c=$(num "$3" 160)
    fp="approveFootprint $a $b $c" ;;
  transferFrom)
    [ $# -eq 5 ] || die "transferFrom takes <balSlot> <allowSlot> <src> <dst> <caller>"
    a=$(num "$1" 128); b=$(num "$2" 128); c=$(num "$3" 160); d=$(num "$4" 160); e=$(num "$5" 160)
    fp="transferFromFootprint $a $b $c $d $e" ;;
  *) die "unknown call kind: '$kind'" ;;
esac

dir=$(mktemp -d); trap 'rm -rf "$dir"' EXIT
cat > "$dir/Check.lean" <<EOF
import Verify.Spec.HashScopeCheck
open SolidCore.Spec
set_option maxRecDepth 100000 in
theorem footprint_premise : ScopedSep ($fp) := scopedSep_of_check (by decide +kernel)
#print axioms footprint_premise
EOF

echo "PREMISE ScopedSep ($fp)"
if ! out=$(lake env lean "$dir/Check.lean" 2>&1); then
  echo "$out" >&2; echo "CHECK failed"; exit 1
fi
echo "$out"
ax=$(echo "$out" | sed -n "s/.*depends on axioms: \[\(.*\)\]/\1/p")
[ -n "$ax" ] || { echo "CHECK no axiom report"; exit 1; }
for x in $(echo "$ax" | tr ',' ' '); do
  case "$x" in propext|Classical.choice|Quot.sound) ;; *) echo "CHECK axiom refused: $x"; exit 1 ;; esac
done
echo "CHECK kernel accepted"
