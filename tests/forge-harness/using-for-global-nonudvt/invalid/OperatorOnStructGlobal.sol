// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// UF1 reject neighbor: an OPERATOR binding still requires the target to be a
// user-defined VALUE type (UDVT). Binding an operator for a struct global is
// rejected -- "Operators can only be implemented for user-defined value types."
// This must stay rejected after UF1 loosens the plain/library global gate.

struct S {
    uint256 x;
}

function add(S memory a, S memory b) pure returns (S memory) {
    return S(a.x + b.x);
}

using {add as +} for S global;

contract OperatorOnStructGlobal {}
