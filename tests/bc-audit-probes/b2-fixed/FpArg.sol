// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;
contract FpArg { function g(fixed128x18) internal pure returns (uint256) { return 1; } function f(fixed128x18 a) external pure returns (uint256) { return g(a); } }
