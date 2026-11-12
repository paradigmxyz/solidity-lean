// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.28;
// refinement: shape=kernel
contract Main {
    uint256 x;
    function set(uint256 v) external {
        x = v;
    }
}
