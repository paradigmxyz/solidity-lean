// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract StorageArrayLengthIncrement {
    uint256[] private arr;

    function bad() external {
        ++arr.length;
    }
}
