// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// Item #2/#6: `x ** y` must be O(log y) and produce the EVM `EXP` result. A
// large runtime exponent under `unchecked` made the old O(y) interpreter loop
// hang; checked exp must still Panic 0x11 at solc's exact overflow point.
contract ExpBySquaringTarget {
    // Runtime operands defeat solc's compile-time constant folding, so this
    // exercises the interpreter's exponentiation, not a literal fold.
    function uncheckedExp(uint256 b, uint256 e) external pure returns (uint256) {
        unchecked { return b ** e; }
    }

    function checkedExp(uint256 b, uint256 e) external pure returns (uint256) {
        return b ** e;
    }

    function uncheckedNarrowWrap(uint8 b, uint8 e) external pure returns (uint8) {
        unchecked { return b ** e; }
    }

    function signedUncheckedNarrowWrap(int8 b, uint8 e) external pure returns (int8) {
        unchecked { return b ** e; }
    }

    function signedCheckedExp(int256 b, uint256 e) external pure returns (int256) {
        return b ** e;
    }
}
