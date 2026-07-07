// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;
contract FpMul { function f(fixed128x18 a, fixed128x18 b) external pure returns (bool) { return (a * b) == a; } }
