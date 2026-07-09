// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// CMP-MIXEDSIGN #86 reject: opposite-sign folded integer-literal equality.
// solc rejects: "Built-in binary operator == cannot be applied to types
// int_const -1 and int_const 1."

contract C {
    function f() public pure returns (bool) {
        return (0 - 1) == 1;
    }
}
