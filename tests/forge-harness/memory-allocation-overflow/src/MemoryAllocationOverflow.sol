// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// Pins solc's oversized-allocation guard: `arrayAllocationSizeFunction`
// (YulUtilFunctions.cpp:2370) opens every `new bytes(n)` / `new T[](n)` with
// `if gt(length, 0xffffffffffffffff) { panic 0x41 }`, so any requested element
// count above 2**64-1 reverts with Panic(0x41) before allocation.
contract MemoryAllocationOverflow {
    function allocBytes(uint256 len) external pure returns (uint256) {
        bytes memory data = new bytes(len);
        return data.length;
    }

    function allocArray(uint256 len) external pure returns (uint256) {
        uint256[] memory data = new uint256[](len);
        return data.length;
    }
}
