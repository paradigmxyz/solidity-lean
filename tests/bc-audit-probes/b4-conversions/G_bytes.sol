// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;
contract G_bytes {
    // uint16(bytes2 var) : 0x1234 -> 4660
    function u16FromB2() external pure returns (uint16) { bytes2 b = 0x1234; return uint16(b); }
    // bytes2(uint16 var) round trip -> 4660
    function b2FromU16() external pure returns (uint16) { uint16 u = 0x1234; bytes2 b = bytes2(u); return uint16(b); }
    // bytes4 -> bytes2 keeps HIGH bytes: 0x12345678 -> 0x1234 = 4660
    function b4NarrowToB2() external pure returns (uint16) { bytes4 x = 0x12345678; bytes2 y = bytes2(x); return uint16(y); }
    // bytes2 -> bytes4 pads RIGHT: 0x1234 -> 0x12340000 = 305397760
    function b2WidenToB4() external pure returns (uint32) { bytes2 x = 0x1234; bytes4 y = bytes4(x); return uint32(y); }
    // bytes4(uint32 var) same width -> 0x12345678 = 305419896
    function b4FromU32() external pure returns (uint32) { uint32 u = 0x12345678; bytes4 b = bytes4(u); return uint32(b); }
}
