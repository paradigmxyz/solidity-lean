// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

enum Color { Red, Green, Blue } // 3 members: 0,1,2

contract EnumConv {
    // in-range: Color(2) -> ok, returns 2
    function enumInRange() external pure returns (uint8) {
        uint8 x = 2;
        Color c = Color(x);
        return uint8(c);
    }
    // out-of-range: Color(3) -> panic 0x21
    function enumOutOfRange() external pure returns (uint8) {
        uint8 x = 3;
        Color c = Color(x);
        return uint8(c);
    }
    // boundary: Color(0) -> 0
    function enumZero() external pure returns (uint8) {
        uint8 x = 0;
        return uint8(Color(x));
    }
}
