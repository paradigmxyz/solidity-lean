// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract ParameterNameOnlyOverload {
    function same(uint256 first) internal pure returns (uint256) {
        return first;
    }

    function same(uint256 second) internal pure returns (uint256) {
        return second + 1;
    }
}
