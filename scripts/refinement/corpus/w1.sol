// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.28;
// refinement: shape=kernel
contract Main {
    function f(uint256 x) external pure returns (uint256) {
        return x + 1;
    }
}
