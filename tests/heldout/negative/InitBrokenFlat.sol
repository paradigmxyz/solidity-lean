// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// Negative inside the envelope: x starts at 0, so the invariant x == 1 does not hold
/// initially; the only function keeps it. Expected: not Certified.
/// @custom:invariant x == 1
contract InitBrokenFlat {
    uint256 public x;

    /// @custom:ensures x == 1
    function one() external {
        x = 1;
    }
}
