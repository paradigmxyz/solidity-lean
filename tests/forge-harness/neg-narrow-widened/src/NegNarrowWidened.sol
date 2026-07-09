// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// Narrow unary-negation widened soundness gap (NEG-NARROW; the unary analogue of
// the G15 binary narrow-arithmetic-widened gap): solc emits `negate_t_intN`, which
// negates at the OPERAND width (`cleanup_t_intN`, then in a checked context guards
// `if eq(value, intN.min) { panic_error_0x11() }`) BEFORE any implicit widening or
// explicit cast to a wider `int`. So `-x` of `type(intN).min` Panics 0x11 in a
// checked block and wraps to `intN.min` in an `unchecked` block, even when the
// result is returned/assigned/cast as a wider `int`. solidity-lean formerly ran the
// checked int256 negation (which never overflows for a narrow `intN.min`) and then
// cleaned at the wider target width, silently producing `-intN.min` in both modes.
contract NegNarrowWidenedHarnessTarget {
    // checked implicit widening: -x of int8 returned as int16.
    function negI8toI16(int8 x) external pure returns (int16) { return -x; }
    // checked explicit cast: int16(-x) must also negate at the int8 operand width.
    function castNegI8toI16(int8 x) external pure returns (int16) { return int16(-x); }
    // unchecked implicit widening: wraps to int8.min instead of panicking.
    function negI8toI16Unchecked(int8 x) external pure returns (int16) {
        unchecked { return -x; }
    }
    // unchecked explicit cast: wraps to int8.min.
    function castNegI8toI16Unchecked(int8 x) external pure returns (int16) {
        unchecked { return int16(-x); }
    }
    // int128.min widened to int256: checked panics, unchecked wraps.
    function negI128toI256(int128 x) external pure returns (int256) { return -x; }
    function negI128toI256Unchecked(int128 x) external pure returns (int256) {
        unchecked { return -x; }
    }
}
