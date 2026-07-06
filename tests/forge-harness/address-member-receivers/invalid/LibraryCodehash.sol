// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

library L {}

contract LibraryCodehash {
    function bad(address target) external view returns (bytes32) {
        return L(target).codehash;
    }
}
