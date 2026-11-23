#!/usr/bin/env bash
# G0's receipts: pinned upstream tools, the frozen cases regenerate unchanged, the production
# modules build, the production closure's axioms are Lean's three (every constant, by
# Lean.collectAxioms), and tampered copies fail while unaltered copies pass.
#
# usage: Verify/SourceText/check.sh SOLC SOLAR_VERIFY [--flag]
#   SOLC          solc 0.8.35 (sha256 pinned below)
#   SOLAR_VERIFY  solar-verify built from solar's crates/verify (sha256 pinned below)
#   --flag        also assemble Flag's record (flag_record.sh), build its instance and audit it
# Exit 0 when every row matches its expectation, 1 otherwise.
set -u
cd "$(dirname "$0")/../.."
solc=$1 verify=$2 flag=${3:-}
here=Verify/SourceText
fail=0
row() { printf '%-40s expected %-4s actual %-4s %s\n' "$1" "$2" "$3" "$([ "$2" = "$3" ] && echo ok || echo MISMATCH)"; [ "$2" = "$3" ] || fail=1; }

# 0. The upstream tools the frozen readings come from.
echo "fa8ac9a32d301ad023a36ee5a29f8e291fe3200c60244e43c142539e82a617f4  $solc" | sha256sum -c --quiet; row "solc 0.8.35 pinned" 0 $?
echo "4468c71522c1e26e15e20808b87f5d4e0e81070602fce1ed2eea02c262cbd464  $verify" | sha256sum -c --quiet; row "solar-verify pinned" 0 $?

# 1. The frozen cases: their bytes, and the upstream frontend's reading, regenerate exactly.
python3 "$here/gen_cases.py" "$solc" "$verify" "$here/Cases/Flag.sol" >/dev/null
sha256sum -c --quiet "$here/CASES.sha256"; row "cases regenerate" 0 $?

# 2. The production modules build.
lake build VerifySourceText >/dev/null 2>&1; row "build VerifySourceText" 0 $?

# 3. The production closure's axioms (Audit.lean: every constant of every Verify.SourceText module).
lean_ok() { lake env lean "$1" >"$2" 2>&1; }
ax=$(mktemp -d)
lean_ok "$here/Audit.lean" "$ax/audit"; row "audit production closure" 0 $?
grep -h "constants audited" "$ax/audit" | sed 's/^/  /'

# 4. Unaltered copies pass; tampered copies fail (outside the tree, never the tree itself).
copy() { local d; d=$(mktemp -d); cp "$here/$1" "$d/T.lean"; echo "$d/T.lean"; }
tamper() { # name file old new
  local f; f=$(copy "$2")
  python3 -c 'import sys; p,o,n=sys.argv[1:4]; s=open(p).read(); assert s.count(o)==1, o; open(p,"w").write(s.replace(o,n))' "$f" "$3" "$4" || { row "$1" 1 setup; return; }
  lean_ok "$f" /dev/null; row "$1" 1 $?
}
control() { local f; f=$(copy "$2"); lean_ok "$f" /dev/null; row "$1" 0 $?; }
control "control: unaltered Tests"    Tests.lean
control "control: unaltered TestRuns" TestRuns.lean
control "control: unaltered Audit"    Audit.lean
tamper "tamper: relay left 7 -> 9"     TestRuns.lean "origRelay_eq origRelay (some (true, [7, 9, 3]))" "origRelay_eq origRelay (some (true, [9, 9, 3]))"
tamper "tamper: swap left 9 -> 7"      TestRuns.lean "swapRelay_eq swapRelay (some (true, [9, 9, 3]))" "swapRelay_eq swapRelay (some (true, [7, 9, 3]))"
tamper "tamper: stamp 17 -> 18"        TestRuns.lean "origSetPair_eq origSetPair (some (true, [1, 2, 17]))" "origSetPair_eq origSetPair (some (true, [1, 2, 18]))"
tamper "tamper: caller reads"          Tests.lean "readCaller_eq readCaller none using Cases.Selectors.selector_eq
theorem caller_closed : read LedgerRelayCaller.bytes = none" "readCaller_eq readCaller (some LedgerRelay.upstream) using Cases.Selectors.selector_eq
theorem caller_closed : read LedgerRelayCaller.bytes = some LedgerRelay.upstream"
tamper "tamper: name sigs as original" Tests.lean '"setPairs(uint256,uint256)", "stamp()"]' '"setPair(uint256,uint256)", "stamp()"]'
# The audit must refuse a native evaluation, a declared axiom and sorry in its closure.
tamper "audit refuses native_decide"   Audit.lean "open Lean Elab Command" "theorem tNative : 2 + 2 = 4 := by native_decide
open Lean Elab Command"
tamper "audit refuses a declared axiom" Audit.lean "open Lean Elab Command" "axiom tAx : 1 = 2
theorem tUse : 1 = 2 := tAx
open Lean Elab Command"
tamper "audit refuses sorry"           Audit.lean "open Lean Elab Command" "theorem tSorry : 1 = 2 := sorry
open Lean Elab Command"

# 5. Flag: the record's modules from the immutable record commit, the instance, its audit.
if [ "$flag" = "--flag" ]; then
  bash "$here/flag_record.sh" >/dev/null; row "flag record assembled and pinned" 0 $?
  lake build VerifySourceTextFlag >/dev/null 2>&1; row "build VerifySourceTextFlag" 0 $?
  lean_ok "$here/AuditFlag.lean" "$ax/auditflag"; row "audit production closure with Flag" 0 $?
  grep -h "constants audited" "$ax/auditflag" | sed 's/^/  /'
else
  echo "Flag: not checked (pass --flag)"
fi
exit $fail
