// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

contract RequireFnReasonHarnessTarget {
    error MyErr(uint256 x);

    function boom() internal pure returns (string memory) {
        return "boom";
    }

    // fn-reason: a bare string-returning function call. solc lowers to
    // Error(string) built from boom()'s returned string, NOT a custom error.
    function f(uint256 x) external pure returns (uint256) {
        require(x > 0, boom());
        return x;
    }

    // declared-error reason: stays a custom-error revert (selector++abi.encode).
    function c(uint256 x) external pure returns (uint256) {
        require(x > 0, MyErr(x));
        return x;
    }

    // string local-variable reason: Error(string).
    function s(uint256 x) external pure returns (uint256) {
        string memory r = "svar";
        require(x > 0, r);
        return x;
    }

    // conditional (ternary) string reason: Error(string).
    function t(uint256 x) external pure returns (uint256) {
        require(x > 0, x > 5 ? "hi" : "lo");
        return x;
    }
}
