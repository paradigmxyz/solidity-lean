// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.28;
contract Main {
    uint8 v;
    uint8 w = 7;
    /// @custom:ensures result == old(v) + x
    /// @custom:ensures v == old(v) + x
    /// @custom:ensures w == (old(w) ^ x)
    /// @custom:succeeds-if v + x < 256
    function add(uint8 x) external returns (uint8) { v += x; w ^= x; return v; }
}
