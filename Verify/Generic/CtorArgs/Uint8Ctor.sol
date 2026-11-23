// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

contract Uint8Ctor {
    uint256 x;

    constructor(uint8 v) {
        x = v;
    }

    function get() external view returns (uint256) {
        return x;
    }
}
