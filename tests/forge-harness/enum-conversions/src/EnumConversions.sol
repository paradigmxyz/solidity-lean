// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// Free (file-level) enum: 3 members -> valid ordinals 0,1,2.
enum Color { Red, Green, Blue }

contract EnumConversions {
    // in-range integer -> enum, via an enum-typed local, then enum -> integer.
    function enumInRange() external pure returns (uint8) {
        uint8 x = 2;
        Color c = Color(x);
        return uint8(c);
    }
    // boundary: Color(0) -> 0
    function enumZero() external pure returns (uint8) {
        uint8 x = 0;
        return uint8(Color(x));
    }
    // enum member -> integer ordinal
    function enumMemberToUint() external pure returns (uint8) {
        Color c = Color.Blue;
        return uint8(c);
    }
    // out-of-range integer -> enum reverts with Panic(0x21). The value comes
    // from a local (not a raw literal) so solc does not reject at compile time.
    function enumOutOfRange() external pure returns (uint8) {
        uint8 x = 3;
        Color c = Color(x);
        return uint8(c);
    }
}
