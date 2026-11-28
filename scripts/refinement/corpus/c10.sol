// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.28;
contract Main { function f(uint8 c) external pure returns (bytes32) { return bytes32(bytes2(0x1234) >> c); } }
