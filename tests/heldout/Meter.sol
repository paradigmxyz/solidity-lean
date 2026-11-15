// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// Held-out (no hand-written proofs), inside the generic source stage at bc6da61b: no
/// constructor, no loop, no mapping, no reason strings, no internal calls, comparisons written
/// with `<`. A running total (checked addition) and a peak.
contract Meter {
    uint256 public total;
    uint256 public peak;

    /// @custom:ensures total == old(total) + v
    /// @custom:ensures (old(peak) < v ==> peak == v) && (!(old(peak) < v) ==> peak == old(peak))
    function record(uint256 v) external {
        total = total + v;
        if (peak < v) {
            peak = v;
        }
    }

    /// @custom:ensures total == 0 && peak == old(peak)
    function clear() external {
        total = 0;
    }
}
