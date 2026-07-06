// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract Bad {
    function bad() external pure returns (uint256) {
        uint256 value = 1;
        uint256 value = 2;
        return value;
    }
}
