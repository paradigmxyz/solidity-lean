// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import {BytesConcatStringLiteral} from "../src/BytesConcatStringLiteral.sol";

contract BytesConcatStringLiteralForgeTest {
    BytesConcatStringLiteral private target = new BytesConcatStringLiteral();

    function requireBytesEq(
        bytes memory actual,
        bytes memory expected,
        string memory label
    ) internal pure {
        require(keccak256(actual) == keccak256(expected), label);
    }

    function testJoinLiteral() public view {
        // "abc" packs as raw UTF-8 (0x616263), bytes4 as its 4 raw bytes.
        requireBytesEq(
            target.joinLiteral(),
            hex"61626301020304",
            "join literal"
        );
    }

    function testJoinUnicode() public view {
        // unicode"é" is StringLiteralType; packs as its UTF-8 bytes 0xc3a9.
        requireBytesEq(target.joinUnicode(), hex"c3a9", "join unicode");
    }
}
