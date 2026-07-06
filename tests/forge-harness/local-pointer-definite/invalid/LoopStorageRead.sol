// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;
contract Bad { uint256[] private values; function bad() external view returns (uint256) { uint256[] storage pointer; while (true) { pointer = values; break; } return pointer.length; } }
