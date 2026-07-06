// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract Bad {
    function bad() external pure returns (uint256) {
        uint256 a;
        uint256 b;
        (a, b) = (, uint256(1));
        return b;
    }
}
