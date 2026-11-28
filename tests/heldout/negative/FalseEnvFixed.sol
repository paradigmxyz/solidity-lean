// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// Negative inside the envelope: the premise is satisfiable in general (chain 424242) but false
/// in the statement's fixed environment, so the false postcondition holds there only vacuously.
/// Expected: not Certified (the premise must be checked against the fixed environment).
contract FalseEnvFixed {
    uint256 public x;

    /// @custom:requires block.chainid == 424242
    /// @custom:ensures x == 8
    function set() external {
        x = 7;
    }
}
