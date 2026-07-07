// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;
contract G_int {
    // int8(uint8 var = 200): high bit set -> -56
    function i8FromU8_200() external pure returns (int8) { uint8 a = 200; return int8(a); }
    // uint8(int8 var = -1) -> 255
    function u8FromI8Neg1() external pure returns (uint8) { int8 a = -1; return uint8(a); }
    // int16(int8 var = -1) sign-extend -> -1
    function i16FromI8Neg1() external pure returns (int16) { int8 a = -1; return int16(a); }
    // int8(int16 var = -200): low 8 bits -> +56
    function i8FromI16Neg200() external pure returns (int8) { int16 x = -200; return int8(x); }
    // int256(uint256 var = 2^255) -> type(int256).min
    function i256FromU256Top() external pure returns (int256) {
        uint256 x = 0x8000000000000000000000000000000000000000000000000000000000000000;
        return int256(x);
    }
}
