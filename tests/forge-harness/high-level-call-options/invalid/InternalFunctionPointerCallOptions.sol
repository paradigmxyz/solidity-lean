// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract Bad {
    function localValue(uint256 x) internal pure returns (uint256) {
        return x;
    }

    function bad() external pure returns (uint256) {
        function(uint256) internal pure returns (uint256) fp = localValue;
        return fp{gas: 1}(3);
    }
}
