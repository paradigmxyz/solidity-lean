// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// SOUNDNESS_GAP sample (SYNTHETIC - see claim.json). solc+EVM return 5 and the
// Forge test asserts it. To exercise the observable comparator's DIFFER branch
// deterministically (the known soundness bugs are being fixed), run_samples.py
// SIMULATES a wrong solidity-lean observable (success|w:999) for this sample, clearly
// marked. The comparator must classify it SOUNDNESS_GAP (lane S, wrong-value).
contract Snd {
    function run() external pure returns (uint256) {
        return 5;
    }
}
