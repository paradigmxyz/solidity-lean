// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// Free (file-level) enum: 2 members -> valid ordinals 0,1.
enum E { A, B }

contract EncPackedLiteral {
    // Every argument carries a definite packed width, so solc accepts each in
    // packed mode: an explicit conversion (uint8(1)), a bool literal (true), a
    // string literal ("ab"), a hex-string literal (hex"cd"), a typed variable
    // (x, a), and an enum value (e). None is a bare number/rational literal.
    function packAll(uint16 x, address a) external pure returns (bytes memory) {
        E e = E.B;
        return abi.encodePacked(uint8(1), true, "ab", hex"cd", x, a, e);
    }

    // Literals with a definite packed width only; deterministic bytes so the
    // interpreter semantics can be pinned. Packed = 01 01 6162 cd.
    //   uint8(1) -> 0x01, true -> 0x01, "ab" -> 0x6162, hex"cd" -> 0xcd.
    function packLiteralsOnly() external pure returns (bytes memory) {
        return abi.encodePacked(uint8(1), true, "ab", hex"cd");
    }
}
