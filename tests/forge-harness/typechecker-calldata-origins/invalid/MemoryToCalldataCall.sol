// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract MemoryToCalldataCall {
    function helper(uint256[] calldata input)
        internal
        pure
        returns (uint256)
    {
        return input.length;
    }

    function bad(uint256[] memory input) public pure returns (uint256) {
        return helper(input);
    }
}
