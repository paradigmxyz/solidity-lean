// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

contract MemFmp {
    function pair(uint256 a, uint256 b) external pure returns (uint256) {
        uint256[2] memory x;
        x[0] = a;
        x[1] = b;
        return x[0] ^ x[1];
    }
}
