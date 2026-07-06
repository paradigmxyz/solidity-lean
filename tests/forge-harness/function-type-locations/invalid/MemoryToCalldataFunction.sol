// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract MemoryToCalldataFunction {
    function target(uint256[] memory values) internal pure returns (uint256) {
        return values.length;
    }

    function bad() internal pure {
        function(uint256[] calldata) internal pure returns (uint256) fn = target;
        fn;
    }
}
