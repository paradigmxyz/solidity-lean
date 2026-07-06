// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract ReferenceViaIrMemoryStorage {
    struct Blob {
        bytes data;
        uint256 tag;
    }

    Blob[] private stored;

    function memoryStructArrayToStorageCopy(Blob[] memory input)
        external
        returns (uint256, uint256)
    {
        delete stored;
        stored = input;
        input[0].data[0] = bytes1(uint8(7));
        input[1].tag = 99;
        return (uint8(stored[0].data[0]) + stored[1].tag,
            uint8(input[0].data[0]) + input[1].tag);
    }
}
