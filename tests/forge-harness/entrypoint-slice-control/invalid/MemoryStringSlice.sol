// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract MemoryStringSlice {
    function bad(string memory input)
        external
        pure
        returns (string memory)
    {
        return input[1:2];
    }
}
