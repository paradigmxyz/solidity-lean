// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// Negative: Clamp.sol with one wrong postcondition (`result > a` where the code returns `a`
/// for x <= a). Expected: not Certified (the spec does not hold of the code).
contract ClampWrongSpec {
    /// @custom:requires a <= b
    /// @custom:ensures result > a && result <= b
    function clamp(uint256 x, uint256 a, uint256 b) public pure returns (uint256 result) {
        if (x < a) return a;
        if (x > b) return b;
        return x;
    }
}
