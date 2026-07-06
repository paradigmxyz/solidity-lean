// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract ConstructorValueTypeMemoryParam {
    constructor(uint256 memory seed) {
        seed;
    }
}
