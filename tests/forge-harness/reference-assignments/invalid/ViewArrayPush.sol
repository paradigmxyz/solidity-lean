// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract ViewArrayPush {
    uint256[] private arr;

    function bad() external view {
        arr.push(1);
    }
}
