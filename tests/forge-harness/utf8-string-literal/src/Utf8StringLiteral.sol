// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// A regular (non-`unicode`) string literal that contains a non-ASCII code
// point via a `\u` escape. solc stores the literal as its UTF-8 bytes, so
// U+00E9 ("e" with acute accent) becomes the two bytes 0xC3 0xA9 - NOT the
// single code-point byte 0xE9. Every observable derived from the literal
// (bytes, length, keccak of the bytes, abi.encodePacked) uses the UTF-8 form.
contract Utf8StringLiteral {
    function literalLength() external pure returns (uint256) {
        return bytes("caf\u00e9").length;
    }

    function literalByteAt(uint256 index) external pure returns (uint256) {
        return uint256(uint8(bytes("caf\u00e9")[index]));
    }

    function literalHash() external pure returns (bytes32) {
        return keccak256(bytes("caf\u00e9"));
    }

    function packedHash() external pure returns (bytes32) {
        return keccak256(abi.encodePacked("caf\u00e9"));
    }
}
