// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// Storage state var, but the literal's bottom-up type is int8[2] (the negative
// element forces a signed common type); int8[2] is NOT implicitly convertible
// to uint256[2] even for a storage copy (sign change). solc REJECTS.
contract StateSignChange {
    uint256[2] arr = [-1, 2];
}
