// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// Negative: a second entrypoint breaks the invariant (reset sets x to 0) while the first and
/// the constructor keep it. Expected: not Certified.
/// @custom:invariant x >= 1
contract InvBroken {
    uint256 public x;

    /// @custom:ensures x == 1
    constructor() {
        x = 1;
    }

    /// @custom:ensures x == old(x) + 1
    function inc() external {
        require(x < type(uint256).max, "max");
        x = x + 1;
    }

    function reset() external {
        x = 0;
    }
}
