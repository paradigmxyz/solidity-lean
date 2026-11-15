// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

interface IOracle {
    function price() external view returns (uint256);
}

/// Outside the envelope: an external call. Expected: BLOCKED (external call).
contract ExternalCall {
    uint256 public last;

    /// @custom:ensures last == old(last) || last != old(last)
    function poll(IOracle o) external {
        last = o.price();
    }
}
