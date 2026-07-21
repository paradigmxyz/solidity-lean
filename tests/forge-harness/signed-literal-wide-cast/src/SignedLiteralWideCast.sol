// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// SIGNED-LITERAL-WIDE-CAST: a signed binary with an UNTYPED-literal operand
// under a WIDE (256-bit) cast (`uint256(y + 10)`) or a unary-minus wrapper
// (`-(y * 2)`, `-(y - z * 2)`) fell to solidity-lean's env-LESS lowering: the
// untyped literal lowered as an unsigned word while the `int` local evaluated
// to a Value.int, so the interpreter's binary arm typeMismatched -> spurious
// Panic 0x00 where solc+EVM compute the real value (13 / -6 / ...). The fix
// routes exactly the signed-literal-mix shapes through the env-aware typed
// lowering (literal typed at the signed common type, operand-width checked
// cleanup, then the explicit 256-bit cast). Controls that must stay unchanged:
// `uint256(y + z)` two typed operands, `-(y - z)` with no literal, bare
// `uint256(y)`, and unsigned `uint256(u + 10)`.
contract SignedLiteralWideCastTarget {
    // The repros: signed local + untyped literal under a wide cast.
    function castAddLit(int256 y) external pure returns (uint256) { return uint256(y + 10); }
    function castMulLit(int256 y) external pure returns (uint256) { return uint256(y * 2); }
    function castLitAdd(int256 y) external pure returns (uint256) { return uint256(10 + y); }
    function castInt128(int128 y) external pure returns (int256) { return int256(y + 10); }
    // Unary minus over a binary containing an untyped literal.
    function negMulLit(int256 y) external pure returns (int256) { return -(y * 2); }
    function negNested(int256 y, int256 z) external pure returns (int256) { return -(y - z * 2); }
    function castNeg(int256 y) external pure returns (int256) { return int256(-(y * 2)); }
    // -(int256.min * 1): the 256-bit negation Panic 0x11 must survive.
    function negMulOne(int256 y) external pure returns (int256) { return -(y * 1); }
    // Controls (already-correct shapes that must keep their lowering).
    function castTwoTyped(int256 y, int256 z) external pure returns (uint256) { return uint256(y + z); }
    function negNoLit(int256 y, int256 z) external pure returns (int256) { return -(y - z); }
    function castBare(int256 y) external pure returns (uint256) { return uint256(y); }
    function castUnsigned(uint256 u) external pure returns (uint256) { return uint256(u + 10); }
}
