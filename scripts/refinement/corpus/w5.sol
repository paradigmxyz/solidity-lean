// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.28;
// refinement: solar-flags=-Ogas shape=kernel
contract Main {
    function f(uint256 a, uint256 b) external pure returns (uint256) {
        return a + b;
    }
}
