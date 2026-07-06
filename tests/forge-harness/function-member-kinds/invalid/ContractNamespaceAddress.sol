// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;
contract C { function f(uint256 value) external pure returns (uint256) { return value; } }
contract Bad { function bad() external pure returns (address) { return C.f.address; } }
