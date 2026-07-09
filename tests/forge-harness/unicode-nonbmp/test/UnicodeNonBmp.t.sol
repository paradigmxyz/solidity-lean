// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import "../src/UnicodeNonBmp.sol";

contract UnicodeNonBmpForgeTest {
    UnicodeNonBmp private target;

    function setUp() public {
        target = new UnicodeNonBmp();
    }

    function testEmojiLength() public view {
        // U+1F600 encodes to 4 UTF-8 bytes.
        require(target.emojiLength() == 4, "emoji length");
    }

    function testEmojiBytes() public view {
        require(target.emojiByteAt(0) == 0xF0, "emoji byte0");
        require(target.emojiByteAt(1) == 0x9F, "emoji byte1");
        require(target.emojiByteAt(2) == 0x98, "emoji byte2");
        require(target.emojiByteAt(3) == 0x80, "emoji byte3");
    }

    function testEmojiHash() public view {
        bytes32 expected = keccak256(hex"f09f9880");
        require(target.emojiHash() == expected, "emoji keccak of bytes");
        require(
            expected ==
                0x367c272ea502ac6e9f085c1baddc52d0ac0224f1b7d1e8621202620efa3ba084,
            "pinned emoji keccak"
        );
    }

    function testMixedLength() public view {
        // 'a'(1) + 你 U+4F60 (3) + 😀 U+1F600 (4) + 'b'(1) == 9.
        require(target.mixedLength() == 9, "mixed length");
    }

    function testMixedBytes() public view {
        require(target.mixedByteAt(0) == 0x61, "mixed 'a'");
        require(target.mixedByteAt(3) == 0xA0, "mixed cjk cont");
        require(target.mixedByteAt(4) == 0xF0, "mixed emoji lead");
        require(target.mixedByteAt(8) == 0x62, "mixed 'b'");
    }

    function testMixedHash() public view {
        bytes32 expected = keccak256(hex"61e4bda0f09f988062");
        require(target.mixedHash() == expected, "mixed keccak of bytes");
        require(
            expected ==
                0x1d57900652a9c0f7da60e61aa038786463531be3cba31334368cd6d6dd78fb89,
            "pinned mixed keccak"
        );
    }
}
