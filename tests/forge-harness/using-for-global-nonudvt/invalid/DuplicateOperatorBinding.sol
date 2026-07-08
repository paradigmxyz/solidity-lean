// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// UF3 reject: binding the same operator for the same type twice is a
// directive-level error (4705 "User-defined binary operator + has more than one
// definition matching the operand type visible in the current scope"), even
// when the operator is never applied.

type T is uint256;

function add1(T a, T b) pure returns (T) {
    return a;
}

function add2(T a, T b) pure returns (T) {
    return b;
}

using {add1 as +} for T global;
using {add2 as +} for T global;

contract DuplicateOperatorBinding {}
