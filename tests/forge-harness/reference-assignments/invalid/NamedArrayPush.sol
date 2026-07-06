// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract NamedArrayPush {
    uint256[] private arr;

    function bad() external {
        arr.push({value: 1});
    }
}
