// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract MutabilityOnlyOverload {
    function same(uint256 input) public pure returns (uint256) {
        return input;
    }

    function same(uint256 input) public view returns (uint256) {
        return input + 1;
    }
}
