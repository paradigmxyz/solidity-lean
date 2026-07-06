// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;
contract Bad { uint256[] private values; function bad(bool choose) external view returns (uint256) { uint256[] storage pointer; if (choose) pointer = values; return pointer.length; } }
