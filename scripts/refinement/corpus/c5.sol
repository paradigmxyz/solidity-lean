// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.28;
contract Main { mapping(uint8 => uint16) m; function inc(uint8 k) external returns (uint16) { m[k] += 300; m[k ^ 1] = k; return m[k]; } }
