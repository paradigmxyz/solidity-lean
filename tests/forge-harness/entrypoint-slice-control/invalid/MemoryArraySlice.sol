// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract MemoryArraySlice {
    function bad(uint256[] memory input)
        external
        pure
        returns (uint256[] memory)
    {
        return input[1:2];
    }
}
