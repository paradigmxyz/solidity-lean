// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// CALL-POSITION — user function calls appearing in loop-CONDITION positions.
// The Executable core represents user calls as STATEMENTS, so a call nested in
// a `for`/`do-while`/`while` condition has no pure-expression lowering. These
// positions were never wired to the internal-call hoisting machinery, so
// solidity-lean formerly over-rejected them at Executable lowering even though
// solc accepts every one. The fix desugars a loop whose condition contains a
// call into the same `while(1) { ...; if(cond) ...; body; post }` shape already
// used for bare `while(f())`, re-evaluating the hoisted call each iteration
// (matching solc). The desugar is gated so a call-free condition keeps today's
// loop node unchanged, and (for `for`/`do-while`) is only applied when the body
// has no bare `continue` (which would otherwise skip the condition re-check).
//
// The condition-call functions use INTERNAL calls (`bound()`), which own-
// contract execution can run, so both acceptance AND runtime semantics are
// pinned. A bare EXTERNAL call in a `while` condition (`this.stillBelow(i)`) is
// also newly accepted; its acceptance (lowering) is pinned by
// importedContractAccepted, and the Forge test exercises its execution against
// real solc/EVM. The contract is self-contained (no user-typed state vars) so
// own-call execution can construct it.
contract CallPositionHarnessTarget {
    // Internal single-return helper used in the condition positions below.
    function bound() internal pure returns (uint256) {
        return 5;
    }

    // Public helper used as a bare external self-call in a while condition.
    function stillBelow(uint256 x) public pure returns (bool) {
        return x < 5;
    }

    // #1 for-condition contains an internal call: `i < bound()`.
    function forCondInternal() external pure returns (uint256) {
        uint256 acc = 0;
        for (uint256 i = 0; i < bound(); i++) {
            acc += i;
        }
        return acc; // 0 + 1 + 2 + 3 + 4 = 10
    }

    // #3 while-condition contains a NESTED internal call: `i < bound()`.
    function whileCondInternal() external pure returns (uint256) {
        uint256 i = 0;
        uint256 acc = 0;
        while (i < bound()) {
            acc += i;
            i += 1;
        }
        return acc; // 10
    }

    // #3 while-condition with an internal call AND a `continue` in the body:
    // `continue` must re-check the call condition. The desugar puts the check
    // at the `while(1)` top, so `continue` correctly re-evaluates it.
    function whileContinueInternal() external pure returns (uint256) {
        uint256 i = 0;
        uint256 acc = 0;
        while (i < bound()) {
            i += 1;
            if (i == 2) {
                continue;
            }
            acc += i;
        }
        return acc; // adds 1, 3, 4, 5 (skips i == 2) = 13
    }

    // #2 do-while-condition contains an internal call: `i < bound()`.
    function doWhileCondInternal() external pure returns (uint256) {
        uint256 i = 0;
        uint256 acc = 0;
        do {
            acc += i;
            i += 1;
        } while (i < bound());
        return acc; // 0 + 1 + 2 + 3 + 4 = 10
    }

    // Nested loops: the outer for-condition has an internal call; the inner
    // loop captures its own `continue`, so the outer desugar guard still fires.
    function nestedForCondInternal() external pure returns (uint256) {
        uint256 acc = 0;
        for (uint256 i = 0; i < bound(); i++) {
            for (uint256 j = 0; j < 2; j++) {
                if (j == 1) {
                    continue;
                }
                acc += 1;
            }
        }
        return acc; // outer 5 iters * (inner adds 1 when j == 0) = 5
    }

    // Bare EXTERNAL call in a while-condition (`this.stillBelow(i)` returns
    // bool). Newly accepted (lowering pinned by importedContractAccepted);
    // executed by the Forge test against the deployed contract.
    function whileBareExternal() external view returns (uint256) {
        uint256 i = 0;
        uint256 acc = 0;
        while (this.stillBelow(i)) {
            acc += i;
            i += 1;
        }
        return acc; // stillBelow(i): i < 5, so i = 0..4, acc = 10
    }
}
