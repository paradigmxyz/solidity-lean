// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract BadFixedPointBitwise {
    function bad(fixed128x18 a, fixed128x18 b)
        external
        pure
        returns (fixed128x18)
    {
        return a & b;
    }
}
