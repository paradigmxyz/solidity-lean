// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// Regression guard: the claim's entry.args must match the function signature.
// Here entry.args = [5] but two() takes TWO params. Solidus fails closed on the
// mismatched call while the EVM would still run — which MUST be REJECT_MALFORMED
// (a fabricated call), never a qualifying COVERAGE_GAP.
contract AC {
    function two(uint256 a, uint256 b) external pure returns (uint256) { return a + b; }
}
