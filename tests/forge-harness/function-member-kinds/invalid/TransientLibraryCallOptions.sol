// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;
library L { function f(uint256 value) external pure returns (uint256) { return value; } }
contract Bad { function bad(address target) external returns (uint256) { return L(target).f{gas: 100000}(1); } }
