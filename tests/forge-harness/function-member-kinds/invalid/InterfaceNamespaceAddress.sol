// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;
interface I { function f(uint256 value) external returns (uint256); }
contract Bad { function bad() external pure returns (address) { return I.f.address; } }
