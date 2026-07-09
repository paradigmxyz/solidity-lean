// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// CE-6a: 1 << 4200 exceeds fitsPrecisionBase2 (4096-bit).
contract ShiftPrecision {
    uint256 public constant BAD = (1 << 4200) >> 4200;
}
