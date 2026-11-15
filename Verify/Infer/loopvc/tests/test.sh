#!/usr/bin/env bash
# Acceptance tests of the loop certificate checker: two structurally different loops proved through
# the same checker (verify_counter's annotated for loop; a held-out while loop with its invariants
# supplied in a certify-invariants file), and negatives that must come out blocked or failed.
#
#   SOLAR_VERIFY=/path/to/solar-verify SOLC=/path/to/solc Verify/Infer/loopvc/tests/test.sh WORKDIR
#
# Run from anywhere; WORKDIR receives the exports and receipts. Exit 0 when every case gives its
# expected status.
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../../.." && pwd)
sv=${SOLAR_VERIFY:?set SOLAR_VERIFY to the solar-verify binary}
mkdir -p "$1"; work=$(cd "$1" && pwd)
lc="$root/Verify/Infer/loopvc/loopcert.py"
fails=0
ok() { echo "ok   $*"; }
bad() { echo "FAIL $*"; fails=$((fails + 1)); }

# export NAME SOURCE: solar-verify's loop-cut export of SOURCE (named relative to the root).
# export NAME SOURCE [DIR]: solar-verify's loop-cut export of SOURCE, named relative to DIR (the
# repository root by default), which the export's manifest names its sources from.
export_of() {
    local dir=${3:-$root}
    rm -rf "$work/$1"; mkdir -p "$work/$1"
    (cd "$dir" && "$sv" --dry-run --no-infer --emit-loopvc "$work/$1/vc" "$2" > "$work/$1/export.log" 2>&1) || true
    echo "$dir" > "$work/$1/root"
    [[ -f "$work/$1/vc/manifest.json" ]]
}
# check NAME UNIT STATUS EXIT [REASON_RE]: run.sh on NAME's export, then UNIT's receipt status.
check() {
    local name=$1 unit=$2 want=$3 want_exit=$4 re=${5:-}
    local code=0
    DISCHARGE_SOURCE_ROOT=$(cat "$work/$name/root") bash "$root/Verify/Infer/loopvc/run.sh" "$work/$name/vc" "$work/$name/out" 600 > "$work/$name/run.log" 2>&1 || code=$?
    local got reason
    got=$(jq -r --arg u "$unit" '.units[] | select(.unit == $u) | .status' "$work/$name/out/receipt.json" 2>/dev/null)
    reason=$(jq -r --arg u "$unit" '.units[] | select(.unit == $u) | (.reason // (.reasons // [] | join("; ")))' "$work/$name/out/receipt.json" 2>/dev/null)
    if [[ $got == "$want" && $code == "$want_exit" && ( -z $re || $reason =~ $re ) ]]; then
        ok "$name: $unit $got (exit $code)${reason:+: $reason}"
    else
        bad "$name: $unit expected $want/exit $want_exit${re:+ /$re/}, got '$got'/exit $code: $reason"
        tail -5 "$work/$name/run.log" | sed 's/^/     /'
    fi
}
src="$work/src"; rm -rf "$src"; mkdir -p "$src"

# 1. verify_counter: Counter.bump, a for loop with annotated invariants and decreases.
export_of counter Certified/verify_counter/verify_counter.sol && check counter Counter.bump proved 0 ||
    bad "counter: no export"

# 2. Held-out: Drain.drain, a while loop counting down with a local accumulator and a named return;
#    the source has no loop annotations, the invariants come from Drain.invariants.json.
cp "$here/heldout/Drain.sol" "$src/Drain.sol"
if python3 "$lc" annotate "$src/Drain.sol" "$here/heldout/Drain.invariants.json" "$src/Drain.annotated.sol" > "$src/Drain.annotate.json"; then
    ok "drain: annotated, deleting the inserted lines restores the source"
else bad "drain: annotate"; fi
if [[ -n ${SOLC:-} ]]; then
    a=$("$SOLC" --bin-runtime --metadata-hash none "$src/Drain.sol" 2>/dev/null | tail -1)
    b=$("$SOLC" --bin-runtime --metadata-hash none "$src/Drain.annotated.sol" 2>/dev/null | tail -1)
    if [[ -n $a && $a == "$b" ]]; then ok "drain: runtime bytecode of the annotated copy equals the source's (${#a} hex chars)"
    else bad "drain: runtime bytecode differs after annotating"; fi
fi
export_of drain Drain.annotated.sol "$src" && check drain Drain.drain proved 0 || bad "drain: no export"

# 3. A supplied invariant that holds on entry but is not preserved: failed, never proved.
sed 's/"moved == 2 \* (n - k)"/"moved <= n - k"/' "$here/heldout/Drain.invariants.json" > "$src/wrong.json"
python3 "$lc" annotate "$src/Drain.sol" "$src/wrong.json" "$src/Wrong.sol" > /dev/null
export_of wrong Wrong.sol "$src" && check wrong Drain.drain failed 1 || bad "wrong: no export"

# 4. No ranking function: blocked (termination has no proof).
jq 'del(.loops[0].decreases)' "$here/heldout/Drain.invariants.json" > "$src/norank.json"
python3 "$lc" annotate "$src/Drain.sol" "$src/norank.json" "$src/NoRank.sol" > /dev/null
export_of norank NoRank.sol "$src" && check norank Drain.drain blocked 3 'rank|decreases' || bad "norank: no export"

# 5. An internal call inside the loop: blocked.
# 6. Two loops in one function: blocked.
cat > "$src/Shapes.sol" <<'EOF'
// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

contract Shapes {
    uint256 public total;

    function step(uint256 x) internal pure returns (uint256) {
        return x + 1;
    }

    /// @custom:requires n <= 1000
    function callInLoop(uint256 n) external {
        uint256 s = 0;
        /// @custom:invariant i <= n
        /// @custom:decreases n - i
        for (uint256 i = 0; i < n; i = step(i)) {
            s += 1;
        }
        total = s;
    }

    /// @custom:requires n <= 1000
    function twoLoops(uint256 n) external {
        uint256 s = 0;
        /// @custom:invariant i <= n
        /// @custom:decreases n - i
        for (uint256 i = 0; i < n; i++) {
            s += 1;
        }
        /// @custom:invariant j <= n
        /// @custom:decreases n - j
        for (uint256 j = 0; j < n; j++) {
            s += 1;
        }
        total = s;
    }
}
EOF
if export_of shapes Shapes.sol "$src"; then
    check shapes Shapes.callInLoop blocked 3 'call'
    check shapes Shapes.twoLoops blocked 3 'loop'
else bad "shapes: no export"; fi

# 7. Tampered exports. A candidate edited in the template module (the invariant's 2 made a 3) no
#    longer instantiates to the unit's obligations, so the kernel rejects its exactness proof: failed.
#    A Horn view that is not the one the cut names: blocked before anything is built.
tamper() { # tamper NAME: a copy of drain's export, without its discharge results
    rm -rf "$work/$1"; mkdir -p "$work/$1"; cp -r "$work/drain/vc" "$work/$1/vc"; rm -rf "$work/$1/vc/discharge"
    cp "$work/drain/root" "$work/$1/root"
}
if [[ -d "$work/drain/vc" ]]; then
    tamper tcand
    sed -i 's/\.app \.mul \[\.int 2,/.app .mul [.int 3,/' "$work/tcand/vc/Drain/drain_loopvc.lean"
    if grep -q '\.int 3,' "$work/tcand/vc/Drain/drain_loopvc.lean"; then check tcand Drain.drain failed 1
    else bad "tcand: the candidate was not edited"; fi
    tamper thorn
    echo '; edited' >> "$work/thorn/vc/Drain/drain.horn.smt2"
    check thorn Drain.drain blocked 3 'Horn'
fi

echo "loopvc tests: $fails failed"
[[ $fails -eq 0 ]]
