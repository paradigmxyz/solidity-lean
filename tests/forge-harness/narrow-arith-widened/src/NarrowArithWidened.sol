// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

// Narrow-arithmetic-widened soundness gap (recorded in the G15 note): solc
// computes a binary arithmetic op at the OPERANDS' common type regardless of a
// wider assignment / return target, so a narrow overflow Panics 0x11 even when
// the result is widened afterwards. Solidus formerly cleaned only at the target
// width and silently produced the (fitting) wide value.
contract NarrowArithWidenedHarnessTarget {
    // uint8 + uint8 assigned/returned as uint16.
    function addU8toU16(uint8 a, uint8 b) external pure returns (uint16) { return a + b; }
    // uint8 * uint8 widened.
    function mulU8toU16(uint8 a, uint8 b) external pure returns (uint16) { return a * b; }
    // int8 + int8 widened to int16.
    function addI8toI16(int8 a, int8 b) external pure returns (int16) { return a + b; }
    // explicit operand widening stays 256-bit (no panic): uint256(a)+uint256(b).
    function addWidenedOperands(uint8 a, uint8 b) external pure returns (uint16) {
        return uint16(uint256(a) + uint256(b));
    }
}
