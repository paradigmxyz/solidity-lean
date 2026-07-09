// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// A `unicode"..."` literal is stored by solc as its UTF-8 bytes. A NON-BMP code
// point (supplementary plane, > U+FFFF) such as U+1F600 GRINNING FACE encodes
// to FOUR UTF-8 bytes 0xF0 0x9F 0x98 0x80 - not a UTF-16 surrogate pair and not
// a single code-point byte. This lane pins those bytes on both solc and the
// imported Lean interpreter. (The importer used to emit a `\uXXXX` surrogate
// pair into the generated Lean source, which Lean decoded to two null bytes;
// this fixture guards that regression.)
contract UnicodeNonBmp {
    // Pure emoji: U+1F600 -> 0xF0 0x9F 0x98 0x80 (4 bytes).
    function emojiLength() external pure returns (uint256) {
        return bytes(unicode"😀").length;
    }

    function emojiByteAt(uint256 index) external pure returns (uint256) {
        return uint256(uint8(bytes(unicode"😀")[index]));
    }

    function emojiHash() external pure returns (bytes32) {
        return keccak256(bytes(unicode"😀"));
    }

    // Mixed ASCII + BMP + non-BMP: 'a' (1) + U+4F60 你 (3) + U+1F600 (4) + 'b'
    // (1) == 9 UTF-8 bytes.
    function mixedLength() external pure returns (uint256) {
        return bytes(unicode"a你😀b").length;
    }

    function mixedByteAt(uint256 index) external pure returns (uint256) {
        return uint256(uint8(bytes(unicode"a你😀b")[index]));
    }

    function mixedHash() external pure returns (bytes32) {
        return keccak256(bytes(unicode"a你😀b"));
    }
}
