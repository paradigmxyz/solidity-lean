// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// `abi.encodePacked(cond ? a : b)` packs the conditional's RESULT using the
// ternary's COMMON (mobile) type width, not the then-branch's. Here the
// then-branch is `uint8` and the else-branch is `uint16`, so the common type
// is `uint16` and the operand is always packed as 2 bytes (no padding beyond
// the common width), regardless of which branch is taken.
contract PackedTernaryWidth {
    function packedHash(bool cond) external pure returns (bytes32) {
        return keccak256(abi.encodePacked(cond ? uint8(0x11) : uint16(0x2233)));
    }
}
