// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// Held-out acceptance contract (no hand-written proofs): a bounded loop with a supplied
/// invariant and variant, and one storage word it updates.
/// @custom:invariant total <= cap
contract StepSum {
    uint256 public total;
    uint256 public cap;

    /// @custom:ensures cap == _cap && total == 0
    constructor(uint256 _cap) {
        cap = _cap;
    }

    /// @custom:requires n < 2 ** 64
    /// @custom:ensures result == n * (n + 1) / 2
    function triangle(uint256 n) public pure returns (uint256 result) {
        uint256 s = 0;
        /// @custom:invariant i <= n
        /// @custom:invariant s == i * (i + 1) / 2
        /// @custom:decreases n - i
        for (uint256 i = 0; i < n; ) {
            i = i + 1;
            s = s + i;
        }
        return s;
    }

    /// @custom:ensures total == old(total) + k
    function add(uint256 k) external {
        require(total + k <= cap, "cap");
        total = total + k;
    }
}
