// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

contract SignedLiteralArithmeticHarnessTarget {
    // int / positive numeric literal (the reported symptom).
    function divPosLit(int256 a) external pure returns (int256) {
        return a / 1e18;
    }

    // int / negative numeric literal, truncated toward zero.
    function divNegLit(int256 a) external pure returns (int256) {
        return a / -2;
    }

    // INT_MIN / -1 overflows the signed range -> Panic(0x11).
    function divIntMin() external pure returns (int256) {
        int256 a = type(int256).min;
        return a / -1;
    }

    // Neighbor operators: literal adopts the signed operand's type.
    function mulLit(int256 a) external pure returns (int256) { return a * 3; }
    function addLit(int256 a) external pure returns (int256) { return a + 5; }
    function subLit(int256 a) external pure returns (int256) { return a - 5; }
    function modLit(int256 a) external pure returns (int256) { return a % 7; }
}
