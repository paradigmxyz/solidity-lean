// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;
library L { function f(uint256 value) external pure returns (uint256) { return value; } }
contract Bad { function bad(address target) external pure returns (bytes memory) { return abi.encodeCall(L(target).f, (1)); } }
