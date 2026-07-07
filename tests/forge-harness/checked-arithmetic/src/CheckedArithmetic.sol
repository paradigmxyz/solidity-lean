// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

contract CheckedArithmeticHarnessTarget {
    function addOverflow(uint256 x) external pure returns (uint256) {
        return type(uint256).max + x;
    }

    function uncheckedAddWrap(uint256 x) external pure returns (uint256) {
        unchecked {
            return type(uint256).max + x;
        }
    }

    function divide(uint256 x, uint256 y) external pure returns (uint256) {
        return x / y;
    }

    // Signed-base exponentiation is legal Solidity (B/C W3 soundness fix).
    function negBaseEven() external pure returns (int256) {
        int256 a = -2;
        return a ** 2;
    }

    function negBaseOdd() external pure returns (int256) {
        int256 a = -2;
        return a ** 3;
    }

    // Signed exp overflowing the result width panics (0x11) in checked mode.
    function negExpOverflow() external pure returns (int8) {
        int8 a = -2;
        return a ** 8;
    }

}
