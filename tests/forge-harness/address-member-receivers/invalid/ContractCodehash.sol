// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract T {}

contract ContractCodehash {
    function bad(T target) external view returns (bytes32) {
        return target.codehash;
    }
}
