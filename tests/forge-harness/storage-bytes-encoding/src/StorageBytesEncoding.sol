// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// Pins solc's malformed storage byte-array guard: `extract_byte_array_length`
// (YulUtilFunctions.cpp:1359) panics with StorageEncodingError (0x22) when
// `eq(outOfPlaceEncoding, lt(length, 32))`.  In the long / out-of-place form
// (slot low bit set) an encoded length below 32 is malformed and reverts
// Panic(0x22) on any read.  Only reachable via a crafted storage word.
contract StorageBytesEncoding {
    bytes public data; // slot 0
    string public text; // slot 1

    function dataLength() external view returns (uint256) {
        return data.length;
    }

    function readData() external view returns (bytes memory) {
        return data;
    }

    function textLength() external view returns (uint256) {
        return bytes(text).length;
    }
}
