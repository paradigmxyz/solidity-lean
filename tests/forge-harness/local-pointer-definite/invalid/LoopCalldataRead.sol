// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;
contract Bad { function bad(bytes calldata input) external pure returns (uint256) { bytes calldata pointer; while (true) { pointer = input; break; } return pointer.length; } }
