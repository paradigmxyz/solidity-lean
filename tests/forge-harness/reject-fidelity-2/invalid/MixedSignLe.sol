// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.35;

// CMP-MIXEDSIGN #86 reject: opposite-sign folded integer-literal comparison
// with larger magnitude. `1-2` folds to int_const -1. solc rejects:
// "Built-in binary operator <= cannot be applied to types int_const -1 and
// int_const 3."

contract C {
    function f() public pure returns (bool) {
        return (1 - 2) <= 3;
    }
}
