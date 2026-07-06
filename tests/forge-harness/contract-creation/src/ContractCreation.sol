// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

contract CreatedChild {
    uint256 private value;

    constructor(uint256 seed) {
        value = seed + 1;
    }

    function read() external view returns (uint256) {
        return value;
    }
}

contract ContractCreationHarnessFactory {
    function make(uint256 seed) external returns (CreatedChild) {
        return new CreatedChild(seed);
    }
}
