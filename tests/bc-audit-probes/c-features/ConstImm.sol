// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;
contract ConstImm {
    uint256 constant C1 = 7;
    uint256 constant C2 = C1 * 3 + 1;      // constant from expression
    uint256 immutable I1;
    uint256 immutable I2;
    constructor(uint256 v) {
        I1 = v;                             // immutable set in ctor
        I2 = C2 + v;                        // immutable from const + arg
    }
    function getC2() external pure returns (uint256) { return C2; }
    function getI1() external view returns (uint256) { return I1; }
    function getI2() external view returns (uint256) { return I2; }
}
