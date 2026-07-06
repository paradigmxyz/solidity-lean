// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract NamedFunctionTypeCall {
    function target(uint256 a) internal pure returns (uint256) {
        return a;
    }

    function bad() internal pure returns (uint256) {
        function(uint256 a) internal pure returns (uint256) fn = target;
        return fn({a: 1});
    }
}
