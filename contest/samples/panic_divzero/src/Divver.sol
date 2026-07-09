// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// Differential probe: checked division by zero must revert with Panic(0x12).
// Distinct panic code from the overflow probe (0x11) — confirms solidity-lean
// emits the EXACT per-operation EVM panic code (revert|panic:18), not a generic
// or shared code. A mismatch would be a fake wrong-revert gap.
contract Divver {
    function f(uint256 a, uint256 b) external pure returns (uint256) {
        return a / b;
    }
}
