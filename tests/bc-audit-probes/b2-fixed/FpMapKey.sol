// SPDX-License-Identifier: MIT
pragma solidity ^0.8.35;
contract FpMapKey { mapping(fixed128x18 => uint256) rates; function f(fixed128x18 a) external view returns (uint256) { return rates[a]; } }
