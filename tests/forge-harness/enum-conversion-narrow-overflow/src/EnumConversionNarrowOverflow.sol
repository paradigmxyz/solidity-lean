// SPDX-License-Identifier: MIT
pragma solidity 0.8.35;

contract EnumConversionNarrowOverflow {
    enum EN { A, B, C }

    function run() external pure returns (uint256) {
        uint8 a = 200;
        uint8 b = 100;
        EN e = EN(a + b);
        return uint256(uint8(e));
    }

    function safe() external pure returns (uint256) {
        uint8 a = 1;
        uint8 b = 1;
        EN e = EN(a + b);
        return uint256(uint8(e));
    }

    function rangeOnly() external pure returns (uint256) {
        uint256 x = 3;
        EN e = EN(x);
        return uint256(uint8(e));
    }
}
