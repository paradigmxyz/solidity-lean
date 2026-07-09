// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// Differential probe: an out-of-range enum conversion must revert with
// Panic(0x21) (0x21 = 33). Distinct panic path (enum bounds on conversion) from
// overflow(0x11)/div-zero(0x12)/OOB(0x32)/assert(0x01). Returns uint256 so the
// return type stays comparable and the PANIC is the observable. A code mismatch
// or a non-panic revert here would be a fake wrong-revert gap.
contract Enumer {
    enum Color { Red, Green, Blue }

    function f(uint8 x) external pure returns (uint256) {
        Color c = Color(x);
        return uint256(uint8(c));
    }
}
