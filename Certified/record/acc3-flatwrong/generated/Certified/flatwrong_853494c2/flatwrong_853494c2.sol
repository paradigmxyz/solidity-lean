// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// Negative control for the branchless-function fallback: `clear` sets `total` to 0 but its
/// spec says 1, so neither tree_meets_map' nor tree_meets_fixed may prove it.
contract FlatWrong {
    uint256 public total;

    /// @custom:succeeds-if msg.value == 0
    /// @custom:ensures total == 1
    function clear() external {
        total = 0;
    }
}
