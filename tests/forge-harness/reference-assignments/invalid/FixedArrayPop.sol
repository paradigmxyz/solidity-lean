// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract FixedArrayPop {
    uint256[2] private arr;

    function bad() external {
        arr.pop();
    }
}
