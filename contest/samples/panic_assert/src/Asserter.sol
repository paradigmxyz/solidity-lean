// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// Differential probe: a failing assert() must revert with Panic(0x01)
// (assertion failure). Distinct panic code from overflow(0x11)/div-zero(0x12)/
// array-OOB(0x32) — confirms per-cause panic-code parity. A mismatch or an
// Error(string)/empty revert here would be a fake wrong-revert gap.
contract Asserter {
    function f(uint256 a) external pure returns (uint256) {
        assert(a != 0);
        return a;
    }
}
