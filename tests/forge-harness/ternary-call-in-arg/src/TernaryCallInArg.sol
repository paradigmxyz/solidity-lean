// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// TERNARY-CALL-IN-ARG (#173) — a ternary containing an internal call, sitting in
// a function-call ARGUMENT position. Before the fix, `double(c ? one() : 2)`
// accepted but failed to lower (`TypeError.unsupported`), poisoning the whole
// contract's executable lowering, because the call-argument hoister only hoisted
// a DIRECT call argument and passed a ternary argument into the pure-argument
// path, which cannot lower a ternary whose branch is a non-pure call. The same
// ternary-with-call already lowered fine as a binary operand, a require
// condition, and in a return. The fix routes a ternary argument through the same
// guarded-branch ternary-call hoister those positions use, binding the ternary
// result to a temp. Self-contained (no user-typed state) so own-call execution
// can construct it.
contract TernaryCallInArgHarnessTarget {
    function one() internal pure returns (uint256) { return 1; }
    function two() internal pure returns (uint256) { return 2; }
    function double(uint256 x) internal pure returns (uint256) { return x * 2; }
    // a * 10 + b, to make left-to-right argument evaluation observable in value.
    function combine(uint256 a, uint256 b) internal pure returns (uint256) {
        return a * 10 + b;
    }

    // DIVERGED (the target bug): call in the THEN branch of a ternary argument.
    // c=true -> double(1) = 2 ; c=false -> double(2) = 4.
    function callThen(bool c) external pure returns (uint256) {
        return double(c ? one() : 2);
    }

    // Call in the FALSE branch of a ternary argument.
    // c=true -> double(9) = 18 ; c=false -> double(2) = 4.
    function callElse(bool c) external pure returns (uint256) {
        return double(c ? 9 : two());
    }

    // Call in BOTH branches of a ternary argument.
    // c=true -> double(1) = 2 ; c=false -> double(2) = 4.
    function callBoth(bool c) external pure returns (uint256) {
        return double(c ? one() : two());
    }

    // Same shape as an assignment RHS (outer call feeds a local declaration).
    // c=true -> 2 ; c=false -> 4.
    function assignRhs(bool c) external pure returns (uint256) {
        uint256 v = double(c ? one() : 2);
        return v;
    }

    // Ternary argument in the SECOND position of a two-argument call: the call
    // in the first argument (`one()`) must evaluate before the ternary's call,
    // preserving solc left-to-right evaluation order. combine(a,b) = a*10 + b.
    // c=true -> combine(1,2) = 12 ; c=false -> combine(1,3) = 13.
    function orderTwoArg(bool c) external pure returns (uint256) {
        return combine(one(), c ? two() : 3);
    }

    // ---- Isolation: must STAY MATCHING (already worked before the fix). ----

    // Ternary of literals as a call argument (no call in branches).
    // c=true -> double(1) = 2 ; c=false -> double(2) = 4.
    function litTernaryArg(bool c) external pure returns (uint256) {
        return double(c ? 1 : 2);
    }

    // Ternary-with-call as a BINARY operand.
    // c=true -> 1 + 10 = 11 ; c=false -> 2 + 10 = 12.
    function binaryOperand(bool c) external pure returns (uint256) {
        return (c ? one() : 2) + 10;
    }

    // Ternary-with-call as a REQUIRE condition.
    function requireCond(bool c) external pure returns (uint256) {
        require((c ? one() : two()) > 0, "positive");
        return 42;
    }

    // Ternary-with-call in a RETURN (both branches calls).
    // c=true -> 1 ; c=false -> 2.
    function returnTernary(bool c) external pure returns (uint256) {
        return c ? one() : two();
    }
}
