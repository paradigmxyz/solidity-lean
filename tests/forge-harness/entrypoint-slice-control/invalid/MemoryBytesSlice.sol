// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract MemoryBytesSlice {
    function bad(bytes memory input)
        external
        pure
        returns (bytes memory)
    {
        return input[1:2];
    }
}
