// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;
contract Bad { function bad(bytes calldata input, bool choose) external pure returns (uint256) { bytes calldata pointer; if (choose) pointer = input; return pointer.length; } }
