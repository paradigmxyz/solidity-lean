// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

import {StringConcatHexLit} from "../src/StringConcatHexLit.sol";

contract StringConcatHexLitForgeTest {
    StringConcatHexLit private target = new StringConcatHexLit();

    function requireStrEq(
        string memory actual,
        string memory expected,
        string memory label
    ) internal pure {
        require(
            keccak256(bytes(actual)) == keccak256(bytes(expected)),
            label
        );
    }

    function testStringConcatHexLiterals() public view {
        requireStrEq(target.joinHex(), "a", "hex61 == a");
        requireStrEq(target.joinMixed(), "ab", "a + hex62 == ab");
        requireStrEq(target.joinXy(), "xy", "x + hex79 == xy");
        // hex"e298ba" decodes to the UTF-8 bytes of the ☺ code point.
        requireStrEq(target.joinMultibyte(), unicode"☺", "hexE298BA == U+263A");
    }
}
