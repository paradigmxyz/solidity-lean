// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract Bad {
    function bad() external pure returns (uint256) {
        uint256 a;
        (a, uint256(1)) = (uint256(1), uint256(2));
        return a;
    }
}
