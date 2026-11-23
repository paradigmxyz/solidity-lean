// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// Negative: the constructor does not establish the invariant (x starts at 0). Every function
/// preserves it, so only the initial check can refuse it. Expected: not Certified.
/// @custom:invariant x >= 1
contract InitBroken {
    uint256 public x;

    /// @custom:ensures x == old(x) + 1
    function inc() external {
        require(x < type(uint256).max, "max");
        x = x + 1;
    }
}
