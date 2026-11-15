// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// Negative control for the tolerant succeeds-if proof: the succeeds-if leaves out that `set`
/// reverts above 100, so "a call meeting the succeeds-if succeeds" is false and must be refused.
contract SuccWrong {
    uint256 public level;

    /// @custom:succeeds-if msg.value == 0
    /// @custom:ensures (x <= 5 ==> level == 2) && (x > 5 ==> level == 1)
    function set(uint256 x) external {
        require(x <= 100);
        if (x > 5) {
            level = 1;
        } else {
            level = 2;
        }
    }
}
