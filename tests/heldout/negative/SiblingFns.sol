// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// Negative: isolation between sibling goals. hi() assumes x > 5 and is correct; lo() assumes
/// x <= 5 and its postcondition is false. lo()'s is provable only if hi()'s premise (or any proof
/// state of its goal) reaches lo()'s goal. Expected: not Certified.
contract SiblingFns {
    uint256 public y;

    /// @custom:requires x > 5
    /// @custom:ensures y == 1
    function hi(uint256 x) external {
        require(x > 5, "hi");
        y = 1;
    }

    /// @custom:requires x <= 5
    /// @custom:ensures y == 1
    function lo(uint256 x) external {
        require(x <= 5, "lo");
        y = 2;
    }
}
