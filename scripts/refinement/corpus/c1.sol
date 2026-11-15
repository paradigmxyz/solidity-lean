// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.28;
// refinement: shape=kernel
contract Main {
    function f(uint8 x) external pure returns (uint8) {
        return x * 3 + 1;
    }
}
