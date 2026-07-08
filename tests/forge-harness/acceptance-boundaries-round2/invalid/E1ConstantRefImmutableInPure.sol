// SPDX-License-Identifier: MIT
pragma solidity 0.8.35;

// E1 (2026-07-08): an immutable initialized by a reference to a `constant`
// (type category is the declared `uint`, NOT RationalNumber) is a `View` read,
// so reading it in a `pure` function is TypeError 2527. Contrast with a plain
// numeric-literal immutable, which stays Pure.
contract E1ConstantRefImmutableInPure {
    uint256 constant A = 5;
    uint256 immutable B = A;

    function f() public pure returns (uint256) {
        return B;
    }
}
