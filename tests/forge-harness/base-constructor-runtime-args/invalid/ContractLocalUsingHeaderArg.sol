// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;

library HeaderMath {
    function plusOne(uint256 value) internal pure returns (uint256) {
        return value + 1;
    }
}

contract RuntimeArgBase {
    uint256 public seed;

    constructor(uint256 value) {
        seed = value;
    }
}

contract Bad is RuntimeArgBase(uint256(1).plusOne()) {
    using HeaderMath for uint128;
}
