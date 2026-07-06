// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

contract RuntimeArgBase {
    uint256 public seed;

    constructor(uint256 value) {
        seed = value;
    }
}

contract Bad is RuntimeArgBase(seed()) {
    function seed() public pure returns (uint256) {
        return 7;
    }
}
