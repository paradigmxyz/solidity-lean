// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// Exercises `bytes(...)`/`string(...)` conversions applied to a NON-bare-
// identifier operand: an element of a memory `string[]` (D-MEM-1 shape 1) and
// a storage-nested `bytes(string(storageBytes))` deep copy (D-MEM-1 shape 2),
// plus a memory alias-through-conversion mutate/observe. Each function returns
// solc's value so Forge and the imported Lean interpreter agree.
contract NestedConversionLowering {
    bytes private stored;

    // Seed storage so the imported Lean witness can establish the same state
    // Forge gets from the constructor path (both set `stored = "hello"`).
    function seed() external {
        stored = "hello";
    }

    // bytes(memoryStringElement).length -- previously over-rejected at lowering.
    function memElemLength() external pure returns (uint256) {
        string[] memory s = new string[](2);
        s[0] = "hi";
        return bytes(s[0]).length; // 2
    }

    // bytes(unsetElement).length == 0
    function memElemEmptyFlag() external pure returns (uint256) {
        string[] memory s = new string[](2);
        s[0] = "hi";
        return bytes(s[1]).length == 0 ? 1 : 0; // 1
    }

    // keccak256(bytes(names[i])) -- hashing a memory string element.
    function keccakBytesElemMatch() external pure returns (uint256) {
        string[] memory names = new string[](1);
        names[0] = "alice";
        return
            keccak256(bytes(names[0])) == keccak256(bytes("alice")) ? 1 : 0; // 1
    }

    // storage-nested bytes(string(storage)) length (deep copy into memory).
    function storageNestedLength() external view returns (uint256) {
        return bytes(string(stored)).length; // 5 for "hello"
    }

    // The storage->memory deep copy is independent from storage.
    function storageNestedIndependent() external view returns (uint256) {
        bytes memory b = bytes(string(stored));
        b[0] = bytes1(uint8(0x58)); // mutate the fresh memory copy -> 'X'
        // storage is unchanged: first byte still 'h' (0x68).
        if (uint8(b[0]) == 0x58 && uint8(stored[0]) == 0x68) {
            return 1;
        }
        return 0;
    }

    // Memory string<->bytes conversion is a pointer reinterpret (alias):
    // mutating through `bytes(s[0])` is observed when reading it back.
    function memAliasThroughConv() external pure returns (uint256) {
        string[] memory s = new string[](1);
        s[0] = "hi";
        bytes memory b = bytes(s[0]);
        b[0] = bytes1(uint8(0x58)); // mutate through the conversion alias
        if (uint8(bytes(s[0])[0]) == 0x58) {
            return 1;
        }
        return 0;
    }
}
