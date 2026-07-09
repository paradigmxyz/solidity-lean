// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// CE-2b: ~0 folds to int_const -1, which cannot implicitly convert to an
// unsigned type. Solidus must fail closed rather than evaluate ~0 at runtime.
contract TildeZeroIntoUint {
    uint256 public constant BAD = ~0;
}
