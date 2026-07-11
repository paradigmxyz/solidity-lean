// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// ADDRESS-FOLDED-CONST-CONVERSION: `address(<folded-const-expr>)` is accepted by
// solc whenever the argument constant-folds to a non-negative integer < 2**160.
// solc `RationalNumberType::isExplicitlyConvertibleTo` (Types.cpp:1050) operates
// on the ALREADY-FOLDED `m_value` for a nonpayable `address` target:
//   m_value == 0 || (!isNegative() && !isFractional() && integerType() && numBits() <= 160)
// Literal-ness is irrelevant, so `address(1 + 1)`, `address(2 * 3)`,
// `address(0x1234 + 1)`, and `address(1 - 1)` (folds to 0) all compile.
// solidity-lean formerly lowered the nonpayable-address arm via
// `Expr.toCoreAddressLiteral?`, which only matched literal NODES and returned
// `none` for any non-literal argument, so a constant-folded arithmetic argument
// was over-rejected (the integer path `uint160(1 + 1)` already folded, so the
// asymmetry was the bug). The fix folds untyped constant number-literal
// EXPRESSIONS in the address arm, mirroring the integer path: accept when the
// folded value is a non-negative integer < 2**160, lowering to that runtime word
// (#170 ADDRESS-FOLDED-CONST-CONVERSION).
contract AddressFoldedConstTarget {
    // address(1 + 1) -- folds to 2.
    function addCast() external pure returns (address) { return address(1 + 1); }
    // address(2 * 3) -- folds to 6.
    function mulCast() external pure returns (address) { return address(2 * 3); }
    // address(0x1234 + 1) -- folds to 0x1235 = 4661.
    function hexAddCast() external pure returns (address) { return address(0x1234 + 1); }
    // address(1 - 1) -- folds to 0 (the always-allowed m_value == 0 branch).
    function subZeroCast() external pure returns (address) { return address(1 - 1); }
    // address(2**160 - 1) -- the accepted boundary (numBits() == 160).
    function maxCast() external pure returns (address) { return address(2 ** 160 - 1); }
    // Plain literal must STILL work: address(2) = 2.
    function plainLit() external pure returns (address) { return address(2); }
}
