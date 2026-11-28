// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

contract ArraySum {
    function sum(uint256[] calldata xs) external pure returns (uint256 s) {
        for (uint256 i = 0; i < xs.length; i++) {
            s += xs[i];
        }
    }
}
