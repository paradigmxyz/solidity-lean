// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import "../src/Utf8StringLiteral.sol";

contract Utf8StringLiteralForgeTest {
    Utf8StringLiteral private target;

    function setUp() public {
        target = new Utf8StringLiteral();
    }

    function testLength() public view {
        // 'c','a','f' (1 byte each) + U+00E9 as UTF-8 0xC3 0xA9 (2 bytes) == 5.
        require(target.literalLength() == 5, "utf8 length");
    }

    function testNonAsciiBytes() public view {
        require(target.literalByteAt(3) == 0xC3, "utf8 lead byte");
        require(target.literalByteAt(4) == 0xA9, "utf8 cont byte");
    }

    function testHash() public view {
        bytes32 expected = keccak256(hex"636166c3a9");
        require(target.literalHash() == expected, "keccak of bytes");
        require(
            expected ==
                0x9513447e2d376aacd434727887590dd448cda8f2d30c4ace903d31fe209f8ad8,
            "pinned keccak"
        );
    }

    function testPackedHash() public view {
        // abi.encodePacked of a string packs its UTF-8 bytes (no length prefix),
        // so the packed hash equals the keccak of bytes(...).
        require(
            target.packedHash() == keccak256(hex"636166c3a9"),
            "packed keccak"
        );
    }
}
