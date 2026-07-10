// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// NEGATIVE-literal sibling of #109 (#111 NEG-LITERAL-COMMON-TYPE). The common
// type of a typed operand and an untyped number literal is
// `commonType(typed, literal->mobileType())` (Types.cpp:286). For a NEGATIVE
// literal, `RationalNumberType::mobileType` is the SMALLEST-fitting SIGNED intN
// (-300 -> int16, -1 -> int8), and `IntegerType::isImplicitlyConvertibleTo`
// (Types.cpp:611-614) forbids ALL signed<->unsigned implicit conversions. So:
//   * an UNSIGNED operand with a negative literal has NO common type -- solc
//     REJECTS `uint8 a * -300` (uint8 not convertible to int16, int16 not to
//     uint8). That case is a rejection witness, not a runtime lane.
//   * a SIGNED operand shares the common type: `int16 a * -300` is int16, so the
//     checked op runs at 16 bits and OVERFLOWS to Panic 0x11 exactly as solc's
//     checked arithmetic, returning the fitting signed value otherwise.
// This contract exercises only the ACCEPTED (signed-operand) side that solc
// emits an AST for; the unsigned-operand rejections live in the acceptance
// witnesses (solidity-lean already rejects them -- the A1 signed/unsigned
// conversion rule composed with the #109 mobile-type widening).
contract NegLiteralCommonTypeHarnessTarget {
    // int16 a * -300: common type int16 (-300's mobile). a=100 -> -30000 fits;
    // a=-100 -> 30000 fits; a=200 -> -60000 < -32768 Panics 0x11; a=-200 ->
    // 60000 > 32767 Panics 0x11.
    function mulI16(int16 a) external pure returns (int256) {
        return a * -300;
    }

    // int8 a * -1: common type int8. The classic INT8_MIN negation overflow:
    // a=-128 -> 128 > 127 Panics 0x11; a=100 -> -100 fits.
    function mulI8Neg1(int8 a) external pure returns (int256) {
        return a * -1;
    }

    // int16 a + -300: common type int16. a=100 -> -200 fits;
    // a=-32700 -> -33000 < -32768 Panics 0x11.
    function addI16Neg300(int16 a) external pure returns (int256) {
        return a + -300;
    }

    // -300 * int16 a: literal on the LEFT, same common type int16. a=50 ->
    // -15000 fits; a=-500 -> 150000 > 32767 Panics 0x11.
    function litMulLeft(int16 a) external pure returns (int256) {
        return -300 * a;
    }
}
