// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.28;
contract Main {
    uint8 x8;
    uint16 y16 = 3;
    uint256 z;
    /// @custom:succeeds-if msg.value == 0 && (x8 * a < 256 && y16 * b < 65536)
    /// @custom:ensures x8 == old(x8) * a
    /// @custom:ensures y16 == old(y16) * b
    /// @custom:ensures z == old(z)
    function m(uint8 a, uint16 b) external { x8 *= a; y16 *= b; }
    /// @custom:succeeds-if msg.value == 0 && (a * b * c < 2 ** 256)
    /// @custom:ensures z == a * b * c
    /// @custom:ensures result == a * b * c
    /// @custom:ensures x8 == old(x8) && y16 == old(y16)
    function n(uint8 a, uint16 b, uint256 c) external returns (uint256) { z = uint256(a) * b * c; return z; }
}
