#!/usr/bin/env bash
# G0's receipts: the frozen cases regenerate unchanged, the modules build, their axioms are
# Lean's (and, for Runs.lean only, native_decide's compiled-evaluation axioms), and tampered expectations fail.
#
# usage: Verify/SourceText/check.sh SOLC SOLAR_VERIFY
#   SOLC          solc 0.8.35 (the pinned upstream frontend's compiler)
#   SOLAR_VERIFY  solar-verify built from solar's crates/verify at the pinned commit
# Exit 0 when every row matches its expectation, 1 otherwise.
set -u
cd "$(dirname "$0")/../.."
solc=$1 verify=$2
here=Verify/SourceText
fail=0
row() { printf '%-34s expected %-4s actual %-4s %s\n' "$1" "$2" "$3" "$([ "$2" = "$3" ] && echo ok || echo MISMATCH)"; [ "$2" = "$3" ] || fail=1; }

# 1. The frozen cases: their bytes, and the upstream frontend's reading, regenerate exactly.
python3 "$here/gen_cases.py" "$solc" "$verify" "$here/Cases/Flag.sol" >/dev/null
sha256sum -c --quiet "$here/CASES.sha256"; row "cases regenerate" 0 $?

# 2. The modules build.
lake build Verify.SourceText.Tests Verify.SourceText.Runs >/dev/null 2>&1; row "build Tests, Runs" 0 $?

# 3. Axioms of every receipt theorem.
ax=$(mktemp -d)
{
  echo "import Verify.SourceText.Runs"
  for t in $(grep -ho '^theorem [A-Za-z_]*_\(agrees\|closed\|rejects\)\|^theorem digest_eq' "$here/Tests.lean" "$here/Runs.lean" | awk '{print $2}' | sort -u); do :; done
  awk '/^namespace (Ledger|FlagCases)$/{ns=$2} /^end (Ledger|FlagCases)$/{ns=""} /^theorem [A-Za-z_]*(_agrees|_closed|_rejects|digest_eq|_eq) /{if(ns!="")print "#print axioms SolidCore.Verify.SourceText.Tests." ns "." $2}' "$here/Tests.lean" "$here/Runs.lean" | sort -u
} > "$ax/Axioms.lean"
lake env lean "$ax/Axioms.lean" > "$ax/out" 2>&1; row "print axioms" 0 $?
# Only Runs.lean's compiled-evaluation theorems (and the rejections built on them) may rest on
# native_decide's per-theorem axiom; everything else is kernel-checked with Lean's three axioms.
runs="Ledger.origSetPair_eq,Ledger.bodySetPair_eq,Ledger.origRelay_eq,Ledger.swapRelay_eq,Ledger.body_rejects,Ledger.swap_rejects,FlagCases.origRaise_eq,FlagCases.bodyRaise_eq,FlagCases.body_rejects"
echo "theorems: $(grep -c "depends on axioms" "$ax/out")"
python3 -I "$here/axioms.py" "$ax/out" "$runs"; row "axioms allowed (native: Runs only)" 0 $?

# 4. Tampered expectations must fail to check (a copy outside the tree, never the tree itself).
tamper() { # name file old new
  local d; d=$(mktemp -d); cp "$here/$2" "$d/T.lean"
  python3 -c 'import sys; p,o,n=sys.argv[1:4]; s=open(p).read(); assert s.count(o)==1, o; open(p,"w").write(s.replace(o,n))' "$d/T.lean" "$3" "$4" || { row "$1" 1 setup; return; }
  lake env lean "$d/T.lean" >/dev/null 2>&1; row "$1" 1 $?
}
control() { # name file: an unaltered copy, checked the same way, must pass
  local d; d=$(mktemp -d); cp "$here/$2" "$d/T.lean"; lake env lean "$d/T.lean" >/dev/null 2>&1; row "$1" 0 $?
}
control "control: unaltered Tests copy" Tests.lean
control "control: unaltered Runs copy"  Runs.lean
tamper "tamper: relay left 7 -> 9"     Runs.lean  "(some (true, [7, 9, 3]))" "(some (true, [9, 9, 3]))"
tamper "tamper: swap left 9 -> 7"      Runs.lean  "(some (true, [9, 9, 3]))" "(some (true, [7, 9, 3]))"
tamper "tamper: caller reads"          Tests.lean "readCaller_eq readCaller none using Cases.Selectors.selector_eq
theorem caller_closed : read LedgerRelayCaller.bytes = none" "readCaller_eq readCaller (some LedgerRelay.upstream) using Cases.Selectors.selector_eq
theorem caller_closed : read LedgerRelayCaller.bytes = some LedgerRelay.upstream"
tamper "tamper: name sigs as original" Tests.lean '"setPairs(uint256,uint256)", "stamp()"]' '"setPair(uint256,uint256)", "stamp()"]'
exit $fail
