// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.28;
contract Main { function f(bytes calldata b) external pure returns (uint256) { return b.length; } }
