// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// Negative inside the envelope: one() is correct and can succeed; two(y) stores a constant under
/// a contradictory premise and claims a false postcondition, true only vacuously. Expected: not
/// Certified (the per-function precondition witness must fail for two()).
contract VacuousSecondFlat {
    uint256 public x;

    /// @custom:succeeds-if msg.value == 0
    /// @custom:ensures x == 1
    function one() external {
        x = 1;
    }

    /// @custom:requires y < 3 && y > 5
    /// @custom:ensures x == 8
    function two(uint256 y) external {
        x = 9;
    }
}
