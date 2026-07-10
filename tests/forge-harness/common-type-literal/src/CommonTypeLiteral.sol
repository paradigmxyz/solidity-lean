// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// Common-type of a narrow typed operand and an untyped number LITERAL that does
// NOT fit it (#109 COMMON-TYPE-LITERAL-MOBILE). solc's `Type::commonType`
// (Types.cpp:286) takes `commonType(narrow, literal->mobileType())`, where
// `RationalNumberType::mobileType` is the literal's SMALLEST-fitting uintN/intN
// (300 -> uint16, 70000 -> uint24), NOT uint256. So checked arithmetic runs at
// that narrow common width: an overflow Panics 0x11 even when the result is
// widened afterwards. solidity-lean formerly widened the literal to uint256 and
// ran the op at 256 bits, missing the overflow Panic (wrong-value) and
// mis-typing the result (its over-reject twin: `a + 300` really is uint16).
contract CommonTypeLiteralHarnessTarget {
    // uint8 a * 300: common type uint16 (300's mobile). a=255 -> 76500 > 65535
    // Panics 0x11; a=200 -> 60000 fits, widened to uint256.
    function mulWiden(uint8 a) external pure returns (uint256) {
        uint256 r = a * 300;
        return r;
    }

    // uint8 a + 300: common type uint16, returned as uint16 (the over-reject
    // twin: solc ACCEPTS this; the model formerly typed it uint256 and rejected
    // the return). a=10 -> 310.
    function addReturnU16(uint8 a) external pure returns (uint16) {
        return a + 300;
    }

    // uint16 a * 70000: 70000's mobile is uint24 (byte-granular), so common type
    // is uint24. a=100 -> 7_000_000 fits uint24; a=1000 -> 70_000_000 >
    // 16_777_215 Panics 0x11. Exercises a non-8/16 mobile width.
    function mulU24(uint16 a) external pure returns (uint32) {
        return a * 70000;
    }
}
