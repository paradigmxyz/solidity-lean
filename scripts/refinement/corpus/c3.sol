// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.28;
contract Main { function f(uint8 x, uint8 s) external pure returns (uint8, uint8, uint8, int8) { unchecked { return (x << s, x >> s, x * x, int8(x) >> (s % 9)); } } }
