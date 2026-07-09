// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// Differential probe: a checked uint256 overflow must revert with Panic(0x11).
// Tests that solidity-lean emits the EXACT EVM panic code (revert|panic:17), not
// a different code / an empty revert — a mismatch would be a fake wrong-revert gap.
contract Panicker {
    function f(uint256 a) external pure returns (uint256) {
        return a + 1;
    }
}
