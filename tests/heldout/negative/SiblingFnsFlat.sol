// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// Negative inside the envelope: hi() is correct under x > 5; lo()'s postcondition is false
/// under x <= 5 and provable only if hi()'s premise or proof state reaches lo()'s goal.
/// Expected: not Certified.
contract SiblingFnsFlat {
    uint256 public y;

    /// @custom:ensures x > 5 ==> y == 1
    function hi(uint256 x) external {
        if (x > 5) {
            y = 1;
        }
    }

    /// @custom:ensures x <= 5 ==> y == 1
    function lo(uint256 x) external {
        if (x > 5) {
            y = 1;
        } else {
            y = 2;
        }
    }
}
