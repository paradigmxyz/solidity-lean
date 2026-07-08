// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

// G4: compile-time out-of-bounds index on a fixed-size array — solc TypeError 3383.
contract G4Array {
    function g(uint[3] memory a) public pure returns (uint) {
        return a[3];
    }
}
