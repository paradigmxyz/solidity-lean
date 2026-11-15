// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// Negative control for a wrong succeeds-if on a branchless function: `halt` always reverts, but
/// its succeeds-if claims every call with no value succeeds, so TreeSucceeds must be refused.
contract FlatSuccWrong {
    uint256 public total;

    /// @custom:succeeds-if msg.value == 0
    /// @custom:ensures total == old(total)
    function halt() external {
        revert();
    }
}
