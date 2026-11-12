// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.28;
contract Main { enum E { A, B, C } function f(E e, bool b) external pure returns (uint8, bool) { return (uint8(e) * 2, b != (e == E.B)); } }
