// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

contract StorageCounterHarnessTarget {
    uint256 private value;

    function read() external view returns (uint256) {
        return value;
    }

    function inc() external {
        value += 1;
    }

    function add(uint256 amount) external {
        value += amount;
    }
}
