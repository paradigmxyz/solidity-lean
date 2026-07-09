// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// CE-6a: 1e2000 is an invalid literal (mantissa exceeds fitsPrecisionBase10).
contract LiteralExponent {
    uint256 public constant BAD = 1e2000 / 1e2000;
}
