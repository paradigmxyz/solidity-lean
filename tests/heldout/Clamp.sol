// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// Held-out acceptance contract (no hand-written proofs): branches and checked arithmetic,
/// pure functions and one guarded storage write.
/// @custom:invariant lo <= hi
contract Clamp {
    uint256 public lo;
    uint256 public hi;
    uint256 public level;

    /// @custom:requires _lo <= _hi
    /// @custom:ensures lo == _lo && hi == _hi && level == _lo
    constructor(uint256 _lo, uint256 _hi) {
        require(_lo <= _hi, "range");
        lo = _lo;
        hi = _hi;
        level = _lo;
    }

    /// @custom:requires a <= b
    /// @custom:ensures result >= a && result <= b
    /// @custom:ensures (x < a ==> result == a) && (x > b ==> result == b) && (a <= x && x <= b ==> result == x)
    function clamp(uint256 x, uint256 a, uint256 b) public pure returns (uint256 result) {
        if (x < a) return a;
        if (x > b) return b;
        return x;
    }

    /// @custom:ensures level >= lo && level <= hi
    /// @custom:ensures (x < lo ==> level == lo) && (x > hi ==> level == hi) && (lo <= x && x <= hi ==> level == x)
    function set(uint256 x) external {
        uint256 l = lo;
        uint256 h = hi;
        if (x < l) {
            level = l;
        } else if (x > h) {
            level = h;
        } else {
            level = x;
        }
    }
}
