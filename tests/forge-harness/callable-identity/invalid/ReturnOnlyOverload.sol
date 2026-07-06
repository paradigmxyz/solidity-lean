// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract ReturnOnlyOverload {
    function same(uint256 input) internal pure returns (uint256) {
        return input;
    }

    function same(uint256 input) internal pure returns (bool) {
        return input == 0;
    }
}
