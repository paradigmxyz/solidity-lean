// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;
contract FpConvUint { function f(fixed128x18 a) external pure returns (uint256) { return uint256(a); } }
