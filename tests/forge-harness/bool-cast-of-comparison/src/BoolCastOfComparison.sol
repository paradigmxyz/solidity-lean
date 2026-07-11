// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// BOOL-CAST-OF-COMPARISON: `bool(1 == 2)` is an IDENTITY conversion. A
// comparison/equality/logical operator over constant operands folds to a
// `bool` constant (solc RationalNumberType / BoolType), NOT to a rational
// number. So `bool(boolExpr)` is bool->bool, which solc accepts. solidity-lean
// formerly classified ANY binary expression over untyped number literals as an
// untyped NUMBER literal (no operator restriction), so `1 == 2`, `1 < 2`,
// `1 < 2 && 2 < 3` were mislabeled as numbers; casting them to `bool` then hit
// the `invalidConversion bool bool` over-reject. The fix restricts the
// untyped-number-literal classification to ARITHMETIC/BITWISE operators only
// (+ - * / % ** & | ^ << >>), which genuinely yield a number; comparison,
// equality, and logical operators do not (#165 BOOL-CAST-OF-COMPARISON).
contract BoolCastOfComparisonTarget {
    // bool(equality) -- identity conversion, folds to false.
    function eqCast() external pure returns (bool) { return bool(1 == 2); }
    // bool(relational) -- folds to true.
    function ltCast() external pure returns (bool) { return bool(1 < 2); }
    // bool(logical-and of two relationals) -- folds to true.
    function andCast() external pure returns (bool) { return bool(1 < 2 && 2 < 3); }
    // bool(logical-not of an equality) -- folds to true.
    function notCast() external pure returns (bool) { return bool(!(1 == 2)); }
    // Arithmetic-literal cast must STILL be treated as an untyped number so its
    // numeric-target conversion and range check keep working: uint8(1 + 2) = 3.
    function arithCast() external pure returns (uint8) { return uint8(1 + 2); }
    // Bitwise-shift-literal cast likewise stays an untyped number: uint16(1 << 3) = 8.
    function shiftCast() external pure returns (uint16) { return uint16(1 << 3); }
}
