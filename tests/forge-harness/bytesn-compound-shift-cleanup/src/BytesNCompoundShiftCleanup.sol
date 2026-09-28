// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

contract BytesNCompoundShiftCleanupTarget {
    bytes4 public stateValue = 0x11223344;
    mapping(uint256 => bytes4) public mapped;
    bytes4[1] public arrayValue;

    constructor() {
        mapped[0] = 0x11223344;
        arrayValue[0] = 0x11223344;
    }

    function localShift() external pure returns (bytes4) {
        bytes4 b = 0x11223344;
        b <<= 8;
        return b;
    }

    function mappingShift() external returns (bytes4) {
        mapped[0] <<= 8;
        return mapped[0];
    }

    function stateShift() external returns (bytes4) {
        stateValue <<= 8;
        return stateValue;
    }

    function arrayShift() external returns (bytes4) {
        arrayValue[0] <<= 8;
        return arrayValue[0];
    }

    function rightShift() external pure returns (bytes4) {
        bytes4 b = 0x11223344;
        b >>= 8;
        return b;
    }
}
