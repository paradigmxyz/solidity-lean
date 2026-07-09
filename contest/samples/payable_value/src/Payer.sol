// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// Differential probe: a payable entry called with msg.value must observe the
// SAME wei on both engines. entry.value flows into the Foundry call{value:...}
// AND the mirrored solidity-lean env -> f() returns msg.value -> success|w:1000.
// A value-channel desync (wrong/zero wei on one side) would be a fake wrong-value gap.
contract Payer {
    function f() external payable returns (uint256) {
        return msg.value;
    }
}
