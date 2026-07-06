// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

contract ConstructorDeployHarnessTarget {
    uint256 private value;

    constructor(uint256 seed) {
        value = seed + 1;
        require(seed < 10, "ctor");
    }

    function read() external view returns (uint256) {
        return value;
    }
}
