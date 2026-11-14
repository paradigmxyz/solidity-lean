// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.28;
contract Main { function sum(uint8 n) external pure returns (uint256 s, uint256 c) { for (uint256 i = 0; i < n; i++) { if (i % 7 == 3) continue; s += i * i; c++; if (s > 100000) break; } } }
