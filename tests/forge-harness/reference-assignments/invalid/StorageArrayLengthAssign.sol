// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract StorageArrayLengthAssign {
    uint256[] private arr;

    function bad() external {
        arr.length = 1;
    }
}
