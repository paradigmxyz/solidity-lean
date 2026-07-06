// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// A negative folded value into an unsigned type must stay REJECTED (solc rule
// (3): signed literal cannot implicitly convert to an unsigned type).
contract NegIntoUint {
    uint256 public constant BAD = 0 - 1; // signed literal -> unsigned type
}
