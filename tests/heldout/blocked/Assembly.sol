// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// Outside the envelope: inline assembly writing storage. Expected: BLOCKED (inline assembly).
contract Assembly {
    uint256 public x;

    /// @custom:ensures x == v
    function set(uint256 v) external {
        assembly {
            sstore(x.slot, v)
        }
    }
}
