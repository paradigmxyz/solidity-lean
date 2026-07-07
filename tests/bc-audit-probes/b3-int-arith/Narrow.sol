// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;
contract Narrow {
    // checked: uint8 255+1 -> panic 0x11
    function u8AddOverflow() external pure returns (uint8) { uint8 a=255; uint8 b=1; return a+b; }
    // checked: uint8 255*2 -> panic 0x11
    function u8MulOverflow() external pure returns (uint8) { uint8 a=255; uint8 b=2; return a*b; }
    // checked: int8 100+100 -> panic 0x11
    function i8AddOverflow() external pure returns (int8) { int8 a=100; int8 b=100; return a+b; }
    // unchecked: uint8 255+1 -> 0
    function u8AddWrap() external pure returns (uint8) { unchecked { uint8 a=255; uint8 b=1; return a+b; } }
    // unchecked: uint8 255*2 -> 254
    function u8MulWrap() external pure returns (uint8) { unchecked { uint8 a=255; uint8 b=2; return a*b; } }
    // unchecked: int8 100+100 -> -56
    function i8AddWrap() external pure returns (int8) { unchecked { int8 a=100; int8 b=100; return a+b; } }
    // uint16 add across byte: 65535+1 checked -> panic
    function u16AddOverflow() external pure returns (uint16) { uint16 a=65535; uint16 b=1; return a+b; }
}
