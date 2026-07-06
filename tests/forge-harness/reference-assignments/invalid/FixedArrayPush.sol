// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract FixedArrayPush {
    uint256[2] private arr;

    function bad() external {
        arr.push(1);
    }
}
