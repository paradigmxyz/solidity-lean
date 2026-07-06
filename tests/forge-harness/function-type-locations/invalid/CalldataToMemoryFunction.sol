// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract CalldataToMemoryFunction {
    function target(uint256[] calldata values) internal pure returns (uint256) {
        return values.length;
    }

    function bad() internal pure {
        function(uint256[] memory) internal pure returns (uint256) fn = target;
        fn;
    }
}
