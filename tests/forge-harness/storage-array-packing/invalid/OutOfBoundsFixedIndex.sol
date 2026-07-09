// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.35;

// solc rejects a compile-time-constant index past a fixed array's bound.
contract OutOfBoundsFixedIndex {
    uint72[7] a;
    function bad() external {
        a[7] = 1;
    }
}
