// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// Held-out loop contract: Euclid's algorithm by subtraction. Unlike Counter's bump, the loop is a
/// while loop with a `!=` guard, a branching body that writes one of two variables, a measure
/// that is a sum rather than a distance, and no storage.
contract Gcd {
    /// @custom:requires a > 0 && b > 0 && a < 1
    /// @custom:ensures r > 0 && r <= a && r <= b
    function gcd(uint256 a, uint256 b) public pure returns (uint256 r) {
        uint256 x = a;
        uint256 y = b;
        /// @custom:invariant x > 0 && y > 0 && x <= a && y <= b
        /// @custom:decreases x + y
        while (x != y) {
            if (x > y) {
                x = x - y;
            } else {
                y = y - x;
            }
        }
        r = x;
    }
}
