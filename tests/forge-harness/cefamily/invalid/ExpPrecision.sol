// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// CE-6a: 2**5000 exceeds fitsPrecisionExp (4096-bit) — rejected before division.
contract ExpPrecision {
    uint256 public constant BAD = 2 ** 5000 / 2 ** 5000;
}
