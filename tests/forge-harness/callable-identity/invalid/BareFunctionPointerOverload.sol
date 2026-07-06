// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract BareFunctionPointerOverload {
    function pick(uint256 input) internal pure returns (uint256) {
        return input + 1;
    }

    function pick(address input) internal pure returns (uint256) {
        return uint160(input);
    }

    function run(uint256 value) external pure returns (uint256) {
        function(uint256) internal pure returns (uint256) fn = pick;
        return fn(value);
    }
}
