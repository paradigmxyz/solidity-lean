// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// LOOP-COND-CALL-CONTINUE (#133) — a `for`/`while`/`do-while` whose CONDITION
// contains a user call (hoisted into a pre-condition statement, cf. the
// call-position family) COMBINED with a bare `continue` in the body. The naive
// `while(1){ ... }` desugar of a hoisted-condition loop sends `continue` to the
// loop top, skipping the `post` step (`for`) or the condition re-check
// (`do-while`) that solc runs. The fix relocates `post`/the check to a
// flag-guarded top of the `while(1)`, so `continue` and normal fall-through
// both route through the hoisted condition-call re-evaluation, matching solc's
// control flow and runtime values. Self-contained (no user-typed state) so
// own-call execution can construct it.
contract LoopcondContinueHarnessTarget {
    // Internal single-return helper used in every loop CONDITION below.
    function bound() internal pure returns (uint256) {
        return 5;
    }

    // Internal single-return helper for a body-position call (also hoisted).
    function addOne(uint256 x) internal pure returns (uint256) {
        return x + 1;
    }

    // for + call-in-condition + bare `continue` nested in an `if`. `continue`
    // must run `post` (i++) then re-check the hoisted `bound()` call.
    function forContinue() external pure returns (uint256 acc) {
        for (uint256 i = 0; i < bound(); i++) {
            if (i % 2 == 0) continue;
            acc += i;
        } // adds odd i in [0,5): 1 + 3 = 4
    }

    // do-while + call-in-condition + `continue`. `continue` must jump to the
    // hoisted condition re-check at the bottom.
    function doWhileContinue() external pure returns (uint256 acc) {
        uint256 i = 0;
        do {
            i++;
            if (i == 2) continue;
            acc += i;
        } while (i < bound()); // i=1..5, skip i==2: 1+3+4+5 = 13
    }

    // while + call-in-condition + `continue` (regression companion to the
    // for/do-while cases; `continue` re-checks the hoisted call at the top).
    function whileContinue() external pure returns (uint256 acc) {
        uint256 i = 0;
        while (i < bound()) {
            i++;
            if (i == 2) continue;
            acc += i;
        } // i=1..5, skip i==2: 1+3+4+5 = 13
    }

    // for + call-in-condition + MULTIPLE bare `continue`s.
    function forMultiContinue() external pure returns (uint256 acc) {
        for (uint256 i = 0; i < bound(); i++) {
            if (i == 1) continue;
            if (i == 3) continue;
            acc += i;
        } // i in {0,2,4}: 0 + 2 + 4 = 6
    }

    // for + call-in-condition + `continue`, and the BODY ALSO has a call
    // (`addOne`) that must be hoisted.
    function forBodyCall() external pure returns (uint256 acc) {
        for (uint256 i = 0; i < bound(); i++) {
            if (i % 2 == 0) continue;
            acc += addOne(i);
        } // odd i: addOne(1) + addOne(3) = 2 + 4 = 6
    }

    // for + call-in-condition + `continue` nested TWO ifs deep.
    function forNestedIfContinue() external pure returns (uint256 acc) {
        for (uint256 i = 0; i < bound(); i++) {
            if (i > 0) {
                if (i % 2 == 1) {
                    continue;
                }
            }
            acc += i;
        } // add i unless (i>0 && odd): i=0(+0),2(+2),4(+4) = 6
    }

    // for + call-in-condition + BOTH `continue` and `break` in the body
    // (break must still exit the whole loop, not the desugar's inner shape).
    function forContinueBreak() external pure returns (uint256 acc) {
        for (uint256 i = 0; i < bound(); i++) {
            if (i == 4) break;
            if (i % 2 == 0) continue;
            acc += i;
        } // i<4, odd: 1 + 3 = 4
    }
}
