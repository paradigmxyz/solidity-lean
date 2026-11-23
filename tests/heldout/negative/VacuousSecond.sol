// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// Negative inside the envelope: the first state-changing function (the non-vacuity witness) is
/// correct; the second has a contradictory premise and a false postcondition, true only
/// vacuously. Expected: not Certified (non-vacuity must hold for every function, not one witness).
contract VacuousSecond {
    uint256 public x;

    /// @custom:ensures x == 1
    function one() external {
        x = 1;
    }

    /// @custom:requires y < 3 && y > 5
    /// @custom:ensures x == 9
    function two(uint256 y) external {
        x = y;
    }
}
