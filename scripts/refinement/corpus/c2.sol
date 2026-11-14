// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.28;
contract Main { function f(int8 a, int8 b) external pure returns (int8, int8) { return (a / b, a % b); } }
