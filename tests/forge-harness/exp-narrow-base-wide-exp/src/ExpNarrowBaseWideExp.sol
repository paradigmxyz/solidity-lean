// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// EXP-NARROW-BASE-WIDE-EXPONENT: `**` is NOT a symmetric binary op. Per solc
// (IntegerType::binaryOperatorResult / Token::Exp, Types.cpp), the RESULT type
// of `base ** e` is the BASE (left-operand) type ONLY -- "ignoring the (larger)
// type of the second operand" (the compile-time warning). The exponent keeps
// its own type and is NOT folded into a common-type computation. So the checked
// exponentiation and its overflow Panic 0x11 run at the BASE width, even when
// the exponent is wider. solidity-lean formerly treated `**` symmetrically:
// it computed the common type of base and exponent (uint8 ** uint16 -> uint16)
// and ran the checked-exp at that wider width, where `2 ** 8 = 256` fits and
// the uint8 Panic 0x11 was silently lost.
contract ExpNarrowBaseWideExpTarget {
    // The repro: uint8 base ** uint16 exponent, returned as uint16.
    function g(uint8 base, uint16 e) external pure returns (uint16) { return base ** e; }
    // Explicit uint16 cast around the same expression -- still base-width checked.
    function h(uint8 base, uint16 e) external pure returns (uint16) { return uint16(base ** e); }
    // Mirror: base WIDER than exponent -- no spurious panic, correct value.
    function mirror(uint16 base, uint8 e) external pure returns (uint16) { return base ** e; }
    // Wide base, narrow exponent: full-width value, no panic.
    function wideBase(uint256 base, uint8 e) external pure returns (uint256) { return base ** e; }
    // Signed narrow base, wider exponent: result type is the BASE type (int8).
    function sgn(int8 base, uint16 e) external pure returns (int16) { return base ** e; }
}
