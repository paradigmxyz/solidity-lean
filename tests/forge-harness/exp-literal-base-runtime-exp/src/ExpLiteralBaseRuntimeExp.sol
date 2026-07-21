// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// EXP-LITERAL-BASE-RUNTIME-EXPONENT: a LITERAL base with a NON-literal
// exponent is typed by solc at the full 256-bit width --
// RationalNumberType::binaryOperatorResult (Types.cpp) resolves
// `<rational> ** <integer>` to uint256 (int256 for a negative literal base),
// NOT the literal's mobile type. Probe: `uint8 e; uint8 r = 2**e;` fails with
// "Type uint256 is not implicitly convertible to uint8". solidity-lean's #164
// fix typed the literal base at its MOBILE type (2 -> uint8, -2 -> int8), so
// the checked exponentiation ran at the narrow width and spuriously
// Panicked 0x11 on `2**e` with e=8 (real EVM: 256) and `(-2)**e` with e=9
// (real EVM: -512). Controls that must stay unchanged: literal-only folds
// (`2**112`, `2**255`, `-2**255`), the shift `1 << e`, a TYPED signed base
// `b ** e`, and narrow typed `x ** y` (base-width Panic 0x11 preserved).
contract ExpLiteralBaseRuntimeExpTarget {
    // The repro: literal base, runtime exponent -> uint256-typed, no panic.
    function litUint(uint8 e) external pure returns (uint256) { return 2 ** e; }
    // Negative literal base, runtime exponent -> int256-typed.
    function litInt(uint8 e) external pure returns (int256) { return (-2) ** e; }
    // 2**256 really does overflow uint256 -> the check still runs at 256 bits.
    function litUintWide(uint16 e) external pure returns (uint256) { return 2 ** e; }
    // Control: literal-only folds stay compile-time constants (uniswap Q112).
    function foldQ112() external pure returns (uint224) { uint224 z = 2 ** 112; return z; }
    function fold255() external pure returns (uint256) { return 2 ** 255; }
    function foldNeg255() external pure returns (int256) { return -2 ** 255; }
    // Control: literal shift base was already uint256.
    function shiftLit(uint8 e) external pure returns (uint256) { return 1 << e; }
    // Control: TYPED signed base keeps its own (int256) type.
    function typedSigned(uint8 e) external pure returns (int256) { int256 b = -2; return b ** e; }
    // Control: narrow typed base ** narrow typed exponent checks at uint8.
    function narrowTyped(uint8 x, uint8 y) external pure returns (uint8) { return x ** y; }
}
