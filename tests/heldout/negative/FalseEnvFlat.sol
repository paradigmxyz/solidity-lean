// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// Negative inside the envelope: a contradictory environment premise makes a false
/// postcondition hold vacuously (no checked arithmetic, so the source stage covers it).
/// Expected: not Certified.
contract FalseEnvFlat {
    uint256 public x;

    /// @custom:requires block.chainid == 1 && block.chainid == 2
    /// @custom:ensures x == 8
    function set() external {
        x = 7;
    }
}
