// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// FAKE-ORACLE ATTACK (review O-1). The Forge test passes trivially and asserts
// NOTHING about run(); the claim's declared_observable LIES (success|w:999).
// run() really returns 5, and solidity-lean returns 5. The adjudicator must MEASURE
// the EVM observable (success|w:5) from the Forge run and diff THAT against
// solidity-lean -> NO_DIVERGENCE (not a fake SOUNDNESS_GAP off the lying claim).
contract Fake {
    function run() external pure returns (uint256) { return 5; }
}
