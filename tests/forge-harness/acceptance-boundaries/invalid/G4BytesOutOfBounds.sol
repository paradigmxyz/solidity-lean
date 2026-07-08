// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

// G4: compile-time out-of-bounds index on a bytesN — solc TypeError 1859.
contract G4Bytes {
    function f(bytes4 b) public pure returns (bytes1) {
        return b[4];
    }
}
