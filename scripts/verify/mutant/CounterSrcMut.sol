// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.28;
contract Counter {
    uint256 x;
    /// @custom:ensures x == old(x) + d
    function inc(uint256 d) external { x += d + 1; }
    function get() external view returns (uint256) { return x; }
}
