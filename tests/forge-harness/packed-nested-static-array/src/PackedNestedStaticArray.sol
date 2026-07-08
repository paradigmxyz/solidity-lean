// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// PK1: solc ACCEPTS abi.encodePacked of a nested STATIC array whose ultimate
// element is a static value type (typeSupportedByOldABIEncoder rejects only a
// dynamically-sized *base* array). Array elements are padded to 32 bytes but
// encoded in-place, so a uint8[2][2] packs to 4 * 32 bytes.
contract PackedNestedStaticArray {
    function packMatrix(uint8[2][2] memory matrix)
        external
        pure
        returns (bytes memory)
    {
        return abi.encodePacked(matrix);
    }

    // A dynamic outer dimension over a static inner array is also accepted by
    // solc (only a dynamically-sized base/element array is rejected).
    function packDynamicOuter(uint8[2][] memory rows)
        external
        pure
        returns (bytes memory)
    {
        return abi.encodePacked(rows);
    }
}
