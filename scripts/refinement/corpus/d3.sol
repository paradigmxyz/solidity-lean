// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.28;
contract Main { struct S { uint8 x; bool y; } function f(S calldata s) external pure returns (uint256) { return s.y ? s.x : 3; } }
