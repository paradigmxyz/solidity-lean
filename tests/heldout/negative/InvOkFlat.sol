// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// Control of InvBrokenFlat.sol: the same contract without reset(), so the invariant holds.
/// Expected: Certified.
/// @custom:invariant x == 1
contract InvOkFlat {
    uint256 public x;

    constructor() {
        x = 1;
    }

    /// @custom:succeeds-if msg.value == 0
    /// @custom:ensures x == 1
    function one() external {
        x = 1;
    }
}
