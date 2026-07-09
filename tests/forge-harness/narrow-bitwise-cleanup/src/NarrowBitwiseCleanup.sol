// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// NARROW-BITWISE-CLEANUP (F1/F2): a bitwise operation on a narrow (`< 256`-bit)
// `uintN`/`intN` cleans at its OPERAND width with a *truncating* cast (solc's
// `cleanup_t_uintN` = `and(x, 2^N-1)`; `cleanup_t_intN` = `signextend`), NEVER a
// checked range-check — even inside a checked block. When the result is then
// WIDENED to a bigger type, solc emits `convert_t_uintM_to_t_uintN(op_at_M)`, so
// the operand-width truncation happens FIRST and the wider cleanup must not
// swallow it.
//
//   * F1 (`<<` widened): `x << k` is computed and cleaned at the LHS width, then
//     widened. A single wide cleanup would skip the operand-width truncation.
//   * F2 (`~` on narrow unsigned): `~x` masks with `cleanup_t_uintN`; routing it
//     through a checked cleanup would Panic 0x11 on the full-width complement.
//
// The controls pin that ARITHMETIC (`+ - * ...`) keeps its checked cleanup (must
// still Panic 0x11), same-width narrow `<<` is unchanged, `~uint256` is a
// full-width no-op mask, and `~intN` is unchanged (already in range).
contract NarrowBitwiseCleanupHarnessTarget {
    // F1: `a(255)` == (255 << 4) & 0xff == 240 (NOT 4080).
    function a(uint8 x) external pure returns (uint16) {
        return x << 4;
    }

    // F1: `b(64)` == signextend8(64 << 1) == signextend8(128) == -128 (NOT 128).
    function b(int8 x) external pure returns (int16) {
        return x << 1;
    }

    // F2: `c(0)` == ~0 & 0xff == 255 (must NOT Panic 0x11).
    function c(uint8 x) external pure returns (uint8) {
        return ~x;
    }

    // F2: `d(0)` == (~0 & 0xff) widened == 255 (must NOT Panic 0x11).
    function d(uint8 x) external pure returns (uint16) {
        return ~x;
    }

    // Control: same-width narrow `<<` was already correct; `255 << 4 -> 240`.
    function shlSameWidth(uint8 x) external pure returns (uint8) {
        uint8 y = x << 4;
        return y;
    }

    // Control: checked ARITHMETIC narrow overflow STILL Panics 0x11.
    // `x = 200`: 200 + 100 == 300 > 255 -> Panic 0x11.
    function addOverflow(uint8 x) external pure returns (uint8) {
        return x + 100;
    }

    // Control: `~uint256(0)` full-width == 2^256 - 1 (no truncation regression).
    function notWide() external pure returns (uint256) {
        return ~uint256(0);
    }

    // Control: `~intN` unchanged (already in range); `notInt(5)` == ~5 == -6.
    function notInt(int8 x) external pure returns (int16) {
        return ~x;
    }
}
