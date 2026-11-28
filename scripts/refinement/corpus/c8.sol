// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.28;
contract Main { function fib(uint8 n) internal pure returns (uint256) { return n < 2 ? n : fib(n - 1) + fib(n - 2); } modifier m(uint8 x) { require(x < 25, "big"); _; } function f(uint8 x) external pure m(x) returns (uint256) { return fib(x % 13); } }
