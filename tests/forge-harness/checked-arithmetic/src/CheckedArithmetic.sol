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
}
