// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract ArrayPopArgument {
    uint256[] private arr;

    function bad() external {
        arr.pop(1);
    }
}
