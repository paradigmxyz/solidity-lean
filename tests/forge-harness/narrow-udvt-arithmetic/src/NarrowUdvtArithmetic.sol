// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// Narrow (N < 256) user-defined value types. `unwrap` yields the underlying
// narrow type, so checked arithmetic on an unwrap result overflows at the
// narrow width (Panic 0x11) exactly like a plain `uintN`/`intN` — H2.
type Small is uint8;
type SmallSigned is int8;
type Big is uint256;

// A narrow UDVT operator whose (checked) body does the unwrap arithmetic; even
// dispatched via `+` the body panics on uint8 overflow.
function smallAdd(Small a, Small b) pure returns (Small) {
    return Small.wrap(Small.unwrap(a) + Small.unwrap(b));
}
using {smallAdd as +} for Small global;

contract NarrowUdvtArithmeticHarnessTarget {
    function addU8(uint8 a, uint8 b) external pure returns (uint8) {
        return Small.unwrap(Small.wrap(a)) + Small.unwrap(Small.wrap(b));
    }

    function addI8(int8 a, int8 b) external pure returns (int8) {
        return SmallSigned.unwrap(SmallSigned.wrap(a))
            + SmallSigned.unwrap(SmallSigned.wrap(b));
    }

    function subI8(int8 a, int8 b) external pure returns (int8) {
        return SmallSigned.unwrap(SmallSigned.wrap(a))
            - SmallSigned.unwrap(SmallSigned.wrap(b));
    }

    function addU8Unchecked(uint8 a, uint8 b) external pure returns (uint8) {
        unchecked {
            return Small.unwrap(Small.wrap(a)) + Small.unwrap(Small.wrap(b));
        }
    }

    // Operator `+` dispatches to smallAdd, whose checked body panics 0x11.
    function addU8Operator(uint8 a, uint8 b) external pure returns (uint8) {
        return Small.unwrap(Small.wrap(a) + Small.wrap(b));
    }

    // A word-width (256-bit) UDVT is unaffected: no narrow overflow.
    function addBig(uint256 a, uint256 b) external pure returns (uint256) {
        return Big.unwrap(Big.wrap(a)) + Big.unwrap(Big.wrap(b));
    }
}
