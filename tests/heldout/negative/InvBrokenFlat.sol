// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// Negative inside the envelope: the constructor establishes x == 1, one() keeps it, and a
/// second entrypoint, reset(), breaks it. Expected: not Certified.
/// @custom:invariant x == 1
contract InvBrokenFlat {
    uint256 public x;

    constructor() {
        x = 1;
    }

    /// @custom:succeeds-if msg.value == 0
    /// @custom:ensures x == 1
    function one() external {
        x = 1;
    }

    function reset() external {
        x = 0;
    }
}
