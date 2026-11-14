// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.28;
contract Main { function f(uint8[] calldata a) external pure returns (uint256) { return a.length == 0 ? 0 : a[0]; } }
