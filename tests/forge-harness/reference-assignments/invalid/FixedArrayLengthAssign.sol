// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract FixedArrayLengthAssign {
    uint256[2] private arr;

    function bad() external {
        arr.length = 1;
    }
}
