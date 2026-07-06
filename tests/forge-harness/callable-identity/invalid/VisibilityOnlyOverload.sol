// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract VisibilityOnlyOverload {
    function same(uint256 input) public pure returns (uint256) {
        return input;
    }

    function same(uint256 input) external pure returns (uint256) {
        return input + 1;
    }
}
