// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// ENV-DIVERGENCE ATTACK (review E-1). Entry returns block.timestamp. Pre-fix,
// Solidus ran from a zero env (returns 0) while Foundry returns its default
// (1) -> a spurious wrong-value SOUNDNESS_GAP. Post-fix the env is PINNED on
// both engines (timestamp=1) so both return 1 -> NO_DIVERGENCE.
contract EnvT {
    function ts() external view returns (uint256) { return block.timestamp; }
}
