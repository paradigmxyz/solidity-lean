// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.28;
contract Main { uint256[] a; function g() internal returns (uint256) { a.push(5); return 1; } function f(uint8 x) external returns (uint256, uint256) { a.push(x); uint256[] memory m = new uint256[](3); m[g()] = x; return (a.length, m[1]); } }
