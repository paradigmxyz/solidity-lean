// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// B4 type-conversion probes. Getters return uint/int so the raw word is an
// unambiguous observable (avoids bytesN internal-representation ambiguity).
contract Conv {
    // ---- bytesN <-> uintM (same width) + truncation/padding direction ----
    // uint16(bytes2(0x1234)) == 0x1234 == 4660
    function u16FromB2() external pure returns (uint16) {
        return uint16(bytes2(0x1234));
    }
    // round trip: uint16(bytes2(uint16(0x1234))) == 4660
    function b2FromU16() external pure returns (uint16) {
        bytes2 b = bytes2(uint16(0x1234));
        return uint16(b);
    }
    // bytes4 -> bytes2 keeps HIGH (left) bytes: 0x12345678 -> 0x1234 == 4660
    function b4NarrowToB2() external pure returns (uint16) {
        bytes4 x = 0x12345678;
        bytes2 y = bytes2(x);
        return uint16(y);
    }
    // bytes2 -> bytes4 pads on the RIGHT: 0x1234 -> 0x12340000 == 305336320
    function b2WidenToB4() external pure returns (uint32) {
        bytes2 x = 0x1234;
        bytes4 y = bytes4(x);
        return uint32(y);
    }
    // bytes4(uint32) same width: 0x12345678 == 305419896
    function b4FromU32() external pure returns (uint32) {
        return uint32(bytes4(uint32(0x12345678)));
    }

    // ---- uintN narrowing (truncates LOW byte) ----
    // uint8(uint256(0x1234)) == 0x34 == 52
    function u8FromU256() external pure returns (uint8) {
        return uint8(uint256(0x1234));
    }
    // uint128(2^200 + 7) keeps low 128 bits == 7
    function u128FromU256() external pure returns (uint128) {
        uint256 x = 0x100000000000000000000000000000000000000000000000007;
        return uint128(x);
    }
    // int256(2^255) == type(int256).min
    function i256FromU256Top() external pure returns (int256) {
        uint256 x = 0x8000000000000000000000000000000000000000000000000000000000000000;
        return int256(x);
    }

    // ---- intN sign behavior / reinterpretation ----
    // int8(uint8(200)): high bit set -> -56
    function i8FromU8_200() external pure returns (int8) {
        return int8(uint8(200));
    }
    // uint8(int8(-1)) == 255
    function u8FromI8Neg1() external pure returns (uint8) {
        return uint8(int8(-1));
    }
    // int16(int8(-1)) sign-extends -> -1
    function i16FromI8Neg1() external pure returns (int16) {
        return int16(int8(-1));
    }
    // int8(int16(-200)): low 8 bits of -200; -200 mod 256 = 56 -> +56
    function i8FromI16Neg200() external pure returns (int8) {
        int16 x = -200;
        return int8(x);
    }
    // uint256(int256(-1)) == 2^256-1
    function u256FromI256Neg1() external pure returns (uint256) {
        return uint256(int256(-1));
    }

    // ---- address <-> uint160 <-> bytes20 ----
    // uint160(address(uint160(V))) round trip
    function u160RoundTrip() external pure returns (uint160) {
        uint160 v = 0x1234567890abcdef1234;
        return uint160(address(v));
    }
    // address -> bytes20 -> uint160
    function b20FromAddr() external pure returns (uint160) {
        address a = address(uint160(0x1234567890abcdef1234));
        bytes20 b = bytes20(a);
        return uint160(b);
    }
    // uint160 -> bytes20 keeps value (same width) -> back to uint160
    function b20FromU160() external pure returns (uint160) {
        uint160 v = 0xffeeddccbbaa99887766;
        return uint160(bytes20(v));
    }

}
