// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.28;
type U is int8;
contract Main { function f(uint8 x) external pure returns (U) { return U.wrap(int8(x)); } }
