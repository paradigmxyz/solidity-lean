// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// Held-out (no hand-written proofs), inside the generic source stage at bc6da61b: no
/// constructor, no loop, no mapping, no internal calls; `require` without a reason (an empty
/// revert, to be told apart from running out of gas). A gate opened and closed in turn.
/// @custom:invariant opened == 0 || opened == 1
contract Gate {
    uint256 public opened;
    uint256 public count;

    /// @custom:requires opened == 0
    /// @custom:ensures opened == 1 && count == old(count) + 1
    function open() external {
        require(opened == 0);
        opened = 1;
        count = count + 1;
    }

    /// @custom:requires opened == 1
    /// @custom:ensures opened == 0 && count == old(count)
    function close() external {
        require(opened == 1);
        opened = 0;
    }
}
